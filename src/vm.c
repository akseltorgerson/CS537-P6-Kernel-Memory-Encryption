#include "param.h"
#include "types.h"
#include "defs.h"
#include "x86.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "elf.h"
#include "ptentry.h"

extern char data[];  // defined by kernel.ld
pde_t *kpgdir;  // for use in scheduler()

/************************************************
 *         Doubly Linked List Functions         *
 * *********************************************/
void
clk_insert(uint vpn, pte_t *pte)
{
  struct proc *currProc = myproc();
    for (;;) {
        // First advance the hand.
        currProc->clk_hand = (currProc->clk_hand + 1) % CLOCKSIZE;

        // Found an empty slot.
        if (currProc->clk_queue[currProc->clk_hand].vpn == -1) {
            currProc->clk_queue[currProc->clk_hand].vpn = vpn;
            currProc->clk_queue[currProc->clk_hand].pte = pte;
            break;
        
        // Else if the page in this slot does not have its ref
        // bit set, evict this one.
        } else if (!(*(currProc->clk_queue[currProc->clk_hand].pte) & PTE_A)) {
            // Encrypt the evicted page.
            mencrypt((char*)currProc->clk_queue[currProc->clk_hand].vpn, 1);
            // Put in the new page.
            currProc->clk_queue[currProc->clk_hand].vpn = vpn;
            currProc->clk_queue[currProc->clk_hand].pte = pte;
            break;

        // Else, clear the ref bit of the page in slot.
        } else {
            *(currProc->clk_queue[currProc->clk_hand].pte) &= (~PTE_A);
        }
    }

    // Decrypt the new page.
    decrypt((char*)vpn);
}

// Removing a page forcefully is tricky because you need to
// shift things around.
// This happens at page deallocation.
void
clk_remove(uint vpn)
{
    struct proc *currProc = myproc();
    int prev_tail = currProc->clk_hand;
    int match_idx = -1;

    // Search for the matching element.
    for (int i = 0; i < CLOCKSIZE; ++i) {
        int idx = (currProc->clk_hand + i) % CLOCKSIZE;
        if (currProc->clk_queue[idx].vpn == vpn) {
            match_idx = idx;
            break;
        }
    }

    if (match_idx == -1) {
        return;
		} else {
			// encrypt the page
			mencrypt((char*)currProc->clk_queue[match_idx].vpn, 1);
		}

    // Shift everything from match_idx+1 to prev_tail to
    // one slot to the left.
    for (int idx = match_idx;
         idx != prev_tail;
         idx = (idx + 1) % CLOCKSIZE) {
        int next_idx = (idx + 1) % CLOCKSIZE;
        currProc->clk_queue[idx].vpn = currProc->clk_queue[next_idx].vpn;
        currProc->clk_queue[idx].pte = currProc->clk_queue[next_idx].pte;
    }

    // Clear the element at prev_tail. Set clk_hand to
    // one entry to the left.
    currProc->clk_queue[prev_tail].vpn = -1;
    currProc->clk_hand = currProc->clk_hand == 0 ? CLOCKSIZE - 1
                             : currProc->clk_hand - 1;
}

// Set up CPU's kernel segment descriptors.
// Run once on entry on each CPU.
void
seginit(void)
{
  struct cpu *c;

  // Map "logical" addresses to virtual addresses using identity map.
  // Cannot share a CODE descriptor for both kernel and user
  // because it would have to have DPL_USR, but the CPU forbids
  // an interrupt from CPL=0 to DPL=3.
  c = &cpus[cpuid()];
  c->gdt[SEG_KCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, 0);
  c->gdt[SEG_KDATA] = SEG(STA_W, 0, 0xffffffff, 0);
  c->gdt[SEG_UCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, DPL_USER);
  c->gdt[SEG_UDATA] = SEG(STA_W, 0, 0xffffffff, DPL_USER);
  lgdt(c->gdt, sizeof(c->gdt));
}

// Return the address of the PTE in page table pgdir
// that corresponds to virtual address va.  If alloc!=0,
// create any required page table pages.
pte_t*
walkpgdir(pde_t *pgdir, const void *va, int alloc)
{
  pde_t *pde;
  pte_t *pgtab;

  pde = &pgdir[PDX(va)];
  if(*pde & PTE_P){
    pgtab = (pte_t*)P2V(PTE_ADDR(*pde));
  } else {
    if(!alloc || (pgtab = (pte_t*)kalloc()) == 0)
      return 0;
    // Make sure all those PTE_P bits are zero.
    memset(pgtab, 0, PGSIZE);
    // The permissions here are overly generous, but they can
    // be further restricted by the permissions in the page table
    // entries, if necessary.
    *pde = V2P(pgtab) | PTE_P | PTE_W | PTE_U;
  }
  return &pgtab[PTX(va)];
}

// Create PTEs for virtual addresses starting at va that refer to
// physical addresses starting at pa. va and size might not
// be page-aligned.
static int
mappages(pde_t *pgdir, void *va, uint size, uint pa, int perm)
{
  char *a, *last;
  pte_t *pte;

  a = (char*)PGROUNDDOWN((uint)va);
  last = (char*)PGROUNDDOWN(((uint)va) + size - 1);
  for(;;){
    if((pte = walkpgdir(pgdir, a, 1)) == 0)
      return -1;
    //TODO: Probably want to do (PTE_P | PTE_E)
    if(*pte & (PTE_P | PTE_E))
      panic("remap");
    *pte = pa | perm | PTE_P;
    if (*pte & (PTE_E)) {
      *pte = (*pte & (~PTE_P));
    } 
    if(a == last)
      break;
    a += PGSIZE;
    pa += PGSIZE;
  }
  return 0;
}

// There is one page table per process, plus one that's used when
// a CPU is not running any process (kpgdir). The kernel uses the
// current process's page table during system calls and interrupts;
// page protection bits prevent user code from using the kernel's
// mappings.
//
// setupkvm() and exec() set up every page table like this:
//
//   0..KERNBASE: user memory (text+data+stack+heap), mapped to
//                phys memory allocated by the kernel
//   KERNBASE..KERNBASE+EXTMEM: mapped to 0..EXTMEM (for I/O space)
//   KERNBASE+EXTMEM..data: mapped to EXTMEM..V2P(data)
//                for the kernel's instructions and r/o data
//   data..KERNBASE+PHYSTOP: mapped to V2P(data)..PHYSTOP,
//                                  rw data + free physical memory
//   0xfe000000..0: mapped direct (devices such as ioapic)
//
// The kernel allocates physical memory for its heap and for user memory
// between V2P(end) and the end of physical memory (PHYSTOP)
// (directly addressable from end..P2V(PHYSTOP)).

// This table defines the kernel's mappings, which are present in
// every process's page table.
static struct kmap {
  void *virt;
  uint phys_start;
  uint phys_end;
  int perm;
} kmap[] = {
 { (void*)KERNBASE, 0,             EXTMEM,    PTE_W}, // I/O space
 { (void*)KERNLINK, V2P(KERNLINK), V2P(data), 0},     // kern text+rodata
 { (void*)data,     V2P(data),     PHYSTOP,   PTE_W}, // kern data+memory
 { (void*)DEVSPACE, DEVSPACE,      0,         PTE_W}, // more devices
};

// Set up kernel part of a page table.
pde_t*
setupkvm(void)
{
  pde_t *pgdir;
  struct kmap *k;

  if((pgdir = (pde_t*)kalloc()) == 0)
    return 0;
  memset(pgdir, 0, PGSIZE);
  if (P2V(PHYSTOP) > (void*)DEVSPACE)
    panic("PHYSTOP too high");
  for(k = kmap; k < &kmap[NELEM(kmap)]; k++)
    if(mappages(pgdir, k->virt, k->phys_end - k->phys_start,
                (uint)k->phys_start, k->perm) < 0) {
      freevm(pgdir);
      return 0;
    }
  return pgdir;
}

// Allocate one page table for the machine for the kernel address
// space for scheduler processes.
void
kvmalloc(void)
{
  kpgdir = setupkvm();
  switchkvm();
}

// Switch h/w page table register to the kernel-only page table,
// for when no process is running.
void
switchkvm(void)
{
  lcr3(V2P(kpgdir));   // switch to the kernel page table
}

// Switch TSS and h/w page table to correspond to process p.
void
switchuvm(struct proc *p)
{
  if(p == 0)
    panic("switchuvm: no process");
  if(p->kstack == 0)
    panic("switchuvm: no kstack");
  if(p->pgdir == 0)
    panic("switchuvm: no pgdir");

  pushcli();
  mycpu()->gdt[SEG_TSS] = SEG16(STS_T32A, &mycpu()->ts,
                                sizeof(mycpu()->ts)-1, 0);
  mycpu()->gdt[SEG_TSS].s = 0;
  mycpu()->ts.ss0 = SEG_KDATA << 3;
  mycpu()->ts.esp0 = (uint)p->kstack + KSTACKSIZE;
  // setting IOPL=0 in eflags *and* iomb beyond the tss segment limit
  // forbids I/O instructions (e.g., inb and outb) from user space
  mycpu()->ts.iomb = (ushort) 0xFFFF;
  ltr(SEG_TSS << 3);
  lcr3(V2P(p->pgdir));  // switch to process's address space
  popcli();
}

// Load the initcode into address 0 of pgdir.
// sz must be less than a page.
void
inituvm(pde_t *pgdir, char *init, uint sz)
{
  char *mem;

  if(sz >= PGSIZE)
    panic("inituvm: more than a page");
  mem = kalloc();
  memset(mem, 0, PGSIZE);
  mappages(pgdir, 0, PGSIZE, V2P(mem), PTE_W|PTE_U);
  memmove(mem, init, sz);
}

// Load a program segment into pgdir.  addr must be page-aligned
// and the pages from addr to addr+sz must already be mapped.
int
loaduvm(pde_t *pgdir, char *addr, struct inode *ip, uint offset, uint sz)
{
  uint i, pa, n;
  pte_t *pte;

  if((uint) addr % PGSIZE != 0)
    panic("loaduvm: addr must be page aligned");
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, addr+i, 0)) == 0)
      panic("loaduvm: address should exist");
    pa = PTE_ADDR(*pte);
    if(sz - i < PGSIZE)
      n = sz - i;
    else
      n = PGSIZE;
    if(readi(ip, P2V(pa), offset+i, n) != n)
      return -1;
  }
  return 0;
}

// Allocate page tables and physical memory to grow process from oldsz to
// newsz, which need not be page aligned.  Returns new size or 0 on error.
int
allocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  char *mem;
  uint a;

  if(newsz >= KERNBASE)
    return 0;
  if(newsz < oldsz)
    return oldsz;

  a = PGROUNDUP(oldsz);
  for(; a < newsz; a += PGSIZE){
    mem = kalloc();
    if(mem == 0){
      cprintf("allocuvm out of memory\n");
      deallocuvm(pgdir, newsz, oldsz);
      return 0;
    }
    memset(mem, 0, PGSIZE);
    if(mappages(pgdir, (char*)a, PGSIZE, V2P(mem), PTE_W|PTE_U) < 0){
      cprintf("allocuvm out of memory (2)\n");
      deallocuvm(pgdir, newsz, oldsz);
      kfree(mem);
      return 0;
    }
  }
  return newsz;
}

// Deallocate user pages to bring the process size from oldsz to
// newsz.  oldsz and newsz need not be page-aligned, nor does newsz
// need to be less than oldsz.  oldsz can be larger than the actual
// process size.  Returns the new process size.
int
deallocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  pte_t *pte;
  uint a, pa;

  if(newsz >= oldsz)
    return oldsz;

  a = PGROUNDUP(newsz);
  for(; a  < oldsz; a += PGSIZE){
    pte = walkpgdir(pgdir, (char*)a, 0);
    if(!pte)
      a = PGADDR(PDX(a) + 1, 0, 0) - PGSIZE;
    // Changed this to include PTE_E
    else if((*pte & (PTE_P | PTE_E)) != 0){
      pa = PTE_ADDR(*pte);
      if(pa == 0)
        panic("kfree");
      char *v = P2V(pa);
      kfree(v);
      *pte = 0;
    }
  }
  return newsz;
}

// Free a page table and all the physical memory pages
// in the user part.
void
freevm(pde_t *pgdir)
{
  uint i;

  if(pgdir == 0)
    panic("freevm: no pgdir");
  deallocuvm(pgdir, KERNBASE, 0);
  for(i = 0; i < NPDENTRIES; i++){
    //TODO: Might need to change this to have PTE_E in it, not sure since not pte
    if(pgdir[i] & PTE_P){
      char * v = P2V(PTE_ADDR(pgdir[i]));
      kfree(v);
    }
  }
  kfree((char*)pgdir);
}

// Clear PTE_U on a page. Used to create an inaccessible
// page beneath the user stack.
void
clearpteu(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  if(pte == 0)
    panic("clearpteu");
  *pte &= ~PTE_U;
}

// Given a parent process's page table, create a copy
// of it for a child.
pde_t*
copyuvm(pde_t *pgdir, uint sz)
{
  pde_t *d;
  pte_t *pte;
  uint pa, i, flags;
  char *mem;

  if((d = setupkvm()) == 0)
    return 0;
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, (void *) i, 0)) == 0)
      panic("copyuvm: pte should exist");
    //TODO: Probably want to have (PTE_P | PTE_E)
    if(!(*pte & (PTE_P | PTE_E)))
      panic("copyuvm: page not present");
    pa = PTE_ADDR(*pte);
    flags = PTE_FLAGS(*pte);
    if((mem = kalloc()) == 0)
      goto bad;
    memmove(mem, (char*)P2V(pa), PGSIZE);
    if(mappages(d, (void*)i, PGSIZE, V2P(mem), flags) < 0) {
      kfree(mem);
      goto bad;
    }
  }
  return d;

bad:
  freevm(d);
  return 0;
}

//PAGEBREAK!
// Map user virtual address to kernel address.
char*
uva2ka(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  // Changed to (PTE_P | PTE_E)
  // 1 0000 0001
  if((*pte & (PTE_P | PTE_E)) == 0)
    return 0;
  if((*pte & PTE_U) == 0)
    return 0;
  return (char*)P2V(PTE_ADDR(*pte));
}

// Copy len bytes from p to user address va in page table pgdir.
// Most useful when pgdir is not the current page table.
// uva2ka ensures this only works for PTE_U pages.
int
copyout(pde_t *pgdir, uint va, void *p, uint len)
{
  char *buf, *pa0;
  uint n, va0;

  buf = (char*)p;
  while(len > 0){
    va0 = (uint)PGROUNDDOWN(va);
    pa0 = uva2ka(pgdir, (char*)va0);
    if(pa0 == 0)
      return -1;
    n = PGSIZE - (va - va0);
    if(n > len)
      n = len;
    memmove(pa0 + (va - va0), buf, n);
    len -= n;
    buf += n;
    va = va0 + PGSIZE;
  }
  return 0;
}
/***********************************************************
*                     Added Functions                      *
***********************************************************/
/*                    Notes:
*    When calling walkpagedir, call with alloc = 0 since don'y want to alloc new pages
*    Get uva go to pa, then pa to kva 
*    V2P goes from ka->pa
*    P2V goes from pa->ka
*    uva2kva combines uva->pa and pa->ka  
*    Two level Page table with root called the pagedirectory
*       - Each entry to the page directory (pde) points to an inner level page table (pte)
*       - Each pte holds the physical address of the virtual page and some flag bits         
*/

//Need to clear the PTE_P bit when setting the PTE_E bit
int mencrypt(char *virtual_addr, int len){
  // Does nothing if len = 0 
  if(len == 0){
    return 0;
  }
  // Error if the length is negative
  if(len < 0){
    return -1;
  }
  pte_t *pte;

  // Now do the encryption
  for(int i = 0; i < len; i++){
		// align the requested VA to get the VA that the page starts at
    char *alignedAddr = (char*)PGROUNDDOWN(((uint)virtual_addr) + i*PGSIZE);
		// convert the UVA (user virtual address) to the corresponding KVA (kernel virtual address)
    char *kernelAddr = uva2ka(myproc()->pgdir, alignedAddr);
    // Added Check from first loop to here since we just keep encrypting and dont encrypt that one page
    if(kernelAddr == 0){
      continue;
    }
    //Pretty sure this has to be alignedAddr not kernelAddr
    pte = walkpgdir(myproc()->pgdir, alignedAddr, 0);

		if (!((*pte & PTE_E) == 0)) {
			// move on if its already encrypted
    	continue;
		}
    
		// Clear the PTE_P bit
    *pte = (*pte) & (~PTE_P);
    // Set the PTE_E bit
    *pte = (*pte) | PTE_E;

		// Encrypt all bits on that page
		for (int j = 0; j < PGSIZE; j++) {
			*(kernelAddr + j) ^= 0xFF;
		} 
  }

  // If we did modifications to any pte, then flush the TLB
  switchuvm(myproc());
  return 0;
}

/*
* Returns -1 when entries is NULL
* Returns the number of elements filled in entries 
*/

int getpgtable(struct pt_entry *entries, int num, int wsetOnly) { // Check if entries is null
  if (entries == 0){
    return -1;
  }
  // Checks that wsetOnly is either 0 or 1
  if(wsetOnly != 0 && wsetOnly != 1){
    return -1;
  }
  pte_t *pte;
  struct proc *currProc = myproc();
  char *currAddr = (char*)PGROUNDDOWN((uint)(currProc->sz));
  int totalPages = currProc->sz / PGSIZE;
  int pagesSearched = 0;
	int numFilled = 0;
  // only fill upto num pages, if there are less valid pages than num, exit after we've searched all pages
	while (numFilled < num && pagesSearched < totalPages) {
    pte = walkpgdir(currProc->pgdir, currAddr, 0);
		if (wsetOnly == 0) {
			if ((*pte & PTE_E) != 0 || (*pte & PTE_P) != 0) {
				entries[numFilled].pdx = PDX(currAddr);
        entries[numFilled].ptx = PTX(currAddr);
        entries[numFilled].ppage = *pte >> PTXSHIFT;
        entries[numFilled].present = (*pte & PTE_P) ? 1 : 0;
        entries[numFilled].writable = (*pte & PTE_W) ? 1 : 0;
        entries[numFilled].user = (*pte & PTE_U) ? 1 : 0;
        entries[numFilled].encrypted = (*pte & PTE_E) ? 1 : 0;
        entries[numFilled].ref = (*pte & PTE_A) ? 1 : 0;
        numFilled++;
			}
		} else {
			if (((*pte & PTE_E) == 0) && ((*pte & PTE_P) != 0)) {
				entries[numFilled].pdx = PDX(currAddr);
        entries[numFilled].ptx = PTX(currAddr);
        entries[numFilled].ppage = *pte >> PTXSHIFT;
        entries[numFilled].present = (*pte & PTE_P) ? 1 : 0;
        entries[numFilled].writable = (*pte & PTE_W) ? 1 : 0;
        entries[numFilled].user = (*pte & PTE_U) ? 1 : 0;
        entries[numFilled].encrypted = (*pte & PTE_E) ? 1 : 0;
        entries[numFilled].ref = (*pte & PTE_A) ? 1 : 0;
        numFilled++;
			}
		}
    pagesSearched++;
    currAddr -= PGSIZE;
  }
	return numFilled;
}

/*
* Returns 0 on success, -1 on error 
*/

int dump_rawphymem(uint physical_addr, char *buffer){
  // Null buffer check
  if(buffer == 0){
    return -1;
  }
  *buffer = *buffer;
  uint alignedAddr = PGROUNDDOWN(physical_addr);
  char *kernelAddr = (char*)P2V(alignedAddr);
  //TODO: Buffer might be encrypted so need a little bit of extra work here
  //This is either (uint)buffer or (uint)&buffer
  return copyout(myproc()->pgdir, (uint)buffer, kernelAddr, (uint)PGSIZE);
}

/*
* Return 0 on success
* Return other values based on other information
*/
int decrypt(char *uva){
  pte_t *pte;
  char *alignedAddr = (char*)PGROUNDDOWN(((uint)uva));
  char *kernelAddr = uva2ka(myproc()->pgdir, alignedAddr);
  //This means that PTE_U == 0 or PTE_E and PTE_P both == 0
  if(kernelAddr == 0){
    return -1;
  }
  pte = walkpgdir(myproc()->pgdir, alignedAddr, 0);
  //Do decryption if PTE_E == 1 && PTE_P == 0 ( could just check PTE_E but this is more robust)
  if(!((*pte & PTE_E) == 0) && ((*pte & PTE_P) == 0)){
    // Set the PTE_P bit
    *pte = (*pte) | PTE_P;
    // Clear the PTE_E bit
    *pte = (*pte) & (~PTE_E);
    // Decrypt all bits on that page
		for (int i = 0; i < PGSIZE; i++) {
			*(kernelAddr + i) ^= 0xFF;
		}
    // Insert page into working set
    //clockInsert((uint) alignedAddr, pte);
    clk_insert((uint) alignedAddr, pte);
    //Success
    return 0; 
  }
  // Shouldn't get here but if we do we know we have some error in our logic for this function
  return -2;
}
//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.


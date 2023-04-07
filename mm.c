// Grzegorz Kodrzycki 332834
// Rozwiązanie wykorzystujące explicit listę i heurystykę nextfita

/*
Bloki składają się z nagłówka, payload'a i ewentualny padding żeby mieć
alligment do wielokrotności 16 Mamy footer i header które mają rozmiar 4 bajtów.

Bloki wolne mają nagłówek wskaźnik na poprzedni i następny wolny blok
(ewentualnie na roota jeśli jest to pierwszy lub ostatni blok) Może się składać
z paddingu żeby rozmiar bloku był wielokrotnością 16.

Funckja malloc
Malloc próbuje  znaleźć wolny blok przy użyciu funckji find_fit która przechodzi
po całej liście wolnych bloków. Jeśli znajdziemy blok który nam odpowiada to go
wykorzystujemy (ewentualnie będziemy musieli go podzielić funkcją splitblk)
Jeśli nie znajdziemy odpowiedniego bloku to zwiększamy stertę funkcją morecore

Funckja free
Najprościej zmieniamy flagę bloku na FREE
Podłączamy go do listy wolnych bloków i sprawdzamy czy ma jakichś wolnych
sąsiadów
*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */
static word_t *root;       /* Punkt zaczepienia listy wolnych bloków*/

/* --=[ boundary tag handling ]=-------------------------------------------- */

// Początek z mm-implicit.c
static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size | flags;
  *(bt_footer(bt)) = size | flags;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  return (void *)bt + bt_size(bt);
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  return (void *)bt - bt_size(bt - 1);
}
// Koniec z mm-implicit.c

// Do handlingu explicit
static inline word_t *link_ptr(word_t ptr) {
  return (word_t *)(ptr | 0x800000000);
}

static inline word_t link_fromptr(word_t *ptr) {
  return (word_t)((unsigned long)ptr & 0xffffffff);
}

static inline word_t forwardval(word_t *bt) {
  return *(bt + 1);
}

static inline word_t backwardval(word_t *bt) {
  return *(bt + 2);
}

static inline word_t *forwardptr(word_t *bt) {
  return link_ptr(forwardval(bt));
}

static inline word_t *backwardptr(word_t *bt) {
  return link_ptr(backwardval(bt));
}

static inline void forward_make(word_t *bt, word_t fd) {
  *(bt + 1) = fd;
}

static inline void backward_make(word_t *bt, word_t bk) {
  *(bt + 2) = bk;
}

// Funkcja która odłącza blok z listy
static inline void bt_unlink(word_t *bt) {
  word_t *fdp = forwardptr(bt);
  word_t *bkp = backwardptr(bt);
  backward_make(fdp, link_fromptr(bkp));
  forward_make(bkp, link_fromptr(fdp));
  if (bt == last)
    last = bkp;
}

// Funkcja która podłącza nowy blok do listy
static inline void bt_link(word_t *bt) {
  forward_make(last, link_fromptr(bt));
  forward_make(bt, link_fromptr(root));
  backward_make(bt, link_fromptr(last));
  backward_make(root, link_fromptr(bt));
  last = bt;
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (size + 2 * sizeof(word_t) + ALIGNMENT - 1) & -ALIGNMENT;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  root = morecore(ALIGNMENT - sizeof(word_t));
  if (!root)
    return -1;
  heap_start = morecore(0);

  heap_end = heap_start;
  last = root;
  bt_link(root);

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
// Stosujemy heurystykę, średnio nie opłaca się przeszukiwać więcej niż 330
// bloków więc po tym czasie wychodzę
static word_t *find_fit(size_t reqsz) {
  int maxsearch = 330, sofar = 0; // 330
  for (word_t *bp = forwardptr(root); bp != root; bp = forwardptr(bp)) {
    sofar++;
    if (bt_size(bp) >= reqsz) {
      return bp;
    }
    if (sofar > maxsearch)
      return NULL;
  }
  return NULL; /*No fit*/
}

#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
}
#endif

// Funkcja splitująca blok
static inline void splitblk(word_t *blk, size_t blksize) {
  size_t size = bt_size(blk);
  bt_unlink(blk);
  bt_make(blk, blksize, USED);
  word_t *nextp = bt_next(blk);
  bt_make(nextp, size - blksize, FREE);
  bt_link(nextp);
}

void *malloc(size_t size) {
  size_t asize = blksz(size); /* Adjusted block size */
  word_t *bp;
  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;

  // Sprawdźmy czy jest miejsce na blok
  bp = find_fit(asize);
  if (bp == NULL) {
    // Nie ma miejsca więc dodajemy, tworzymy i przesuwamy heap_end
    bp = morecore(asize);
    bt_make(bp, asize, USED);
    heap_end = bt_footer(bp) + 1;
  } else if (bt_size(bp) > asize) {
    // Znaleźliśmy miejsce i wolne jest więcej niż potrzebujemy więc rozdzielimy
    // bloki
    splitblk(bp, asize);
  } else {
    // Jest idealnie miejsca więc zmieniamy tylko flagę na USED i odłączamy blok
    // z listy wolnych bloków
    bt_make(bp, asize, USED);
    bt_unlink(bp);
  }
  return bt_payload(bp);
}

/* --=[ free ]=------------------------------------------------------------- */

// Funckja łącząca bloki
static inline void joinblk(word_t *blk, size_t size) {
  // Patrz w prawo
  // bt_next(blk) jest dla sprawdzenia czy nie jesteśmy na ostatnim
  // bloku, jeśli tak to na pewno nie ma bloku na prawo
  if (bt_next(blk) != heap_end && bt_free(bt_next(blk))) {
    word_t *nextp = bt_next(blk);
    size += bt_size(nextp);

    // Istnieje wolny blok na prawo więc odłączmy oba połączmy w jeden i dodajmy
    // jako nowy
    bt_unlink(blk);
    bt_unlink(nextp);

    bt_make(blk, size, FREE);
    bt_link(blk);
  }
  // Patrz lewo
  // Analogicznie jak  wyżej
  if (blk != heap_start && bt_free(bt_prev(blk))) {
    word_t *prevp = bt_prev(blk);
    size += bt_size(prevp);

    bt_unlink(blk);
    bt_unlink(prevp);

    bt_make(prevp, size, FREE);
    bt_link(prevp);
  }
}

void free(void *ptr) {
  if (ptr != NULL) {
    // Zdobywamy rozmiar bloku i oznaczamy na FREE
    // Następnie podłączamy da listy i patrzymy czy można z czymś połączyć
    word_t *blk = bt_fromptr(ptr);
    size_t size = bt_size(blk);
    bt_make(blk, size, FREE);
    bt_link(blk);
    joinblk(blk, size);
  }
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  // Analogicznie jak w treści projektu
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  // Analogicznie jak w treści projektu
  if (old_ptr == NULL) {
    return malloc(size);
  }

  // Optymalizacja
  void *new_ptr = old_ptr;
  word_t *old_bt = bt_fromptr(old_ptr);
  size_t asize = blksz(size);
  size_t old_size = bt_size(old_bt);

  // Jeśli rozmiar jest taki sam to nic nie trzeba robić
  if (asize == old_size) {
    return new_ptr;
  } else if (asize < old_size) {
    // Jeśli chcemy zaalokować mniej niż jest w danym miejscu
    // To splitujemy blok i próbujemy połączyć jeśli jest sąsiedni FREE
    bt_make(old_bt, asize, USED);
    word_t *nextp = bt_next(old_bt);
    bt_make(nextp, old_size - asize, FREE);
    bt_link(nextp);
    joinblk(nextp, old_size - asize);
    return old_ptr;
  } else if (bt_next(old_bt) == heap_end) {
    // Alokujemy na ostatnim bloku
    // Dzięki temu możemy trochę mniej dołożyć jeśli jest wolny
    // Dodajemy tylko to co jest potrzebne i update heapend
    size_t need = asize - old_size;
    morecore(need);
    bt_make(old_bt, asize, USED);
    heap_end = bt_footer(old_bt) + 1;
    return old_ptr;
  }

  // Jak opt nie wypali to robimy jak opis projektu przykazał
  new_ptr = malloc(size);

  if (new_ptr == NULL)
    return NULL;

  word_t *blk = bt_fromptr(old_ptr);
  old_size = bt_size(blk);

  if (size < old_size)
    old_size = size;

  memcpy(new_ptr, old_ptr, old_size);

  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
}

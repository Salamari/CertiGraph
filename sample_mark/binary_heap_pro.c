#include "binary_heap_pro.h"
extern void * mallocN (int n); /* Maybe there are better choices for allocators? */

#define ROOT_IDX       0u
#define LEFT_CHILD(x)  (2u * x) + 1u
#define RIGHT_CHILD(x) LEFT_CHILD(x) + 1u
#define PARENT(x)      (x - 1u) / 2u

/* I'm assuming a decent compiler will inline the next two functions; if not they can be made #define macros. */
void exch(unsigned int j, unsigned int k, Item arr[], unsigned int lookup[]) {
  int priority = arr[j].priority;
  void* data = arr[j].data;
  unsigned int key1 = arr[j].key;
  unsigned int key2 = arr[k].key;
  arr[j].priority = arr[k].priority;
  arr[j].data = arr[k].data;
  arr[j].key = key2;
  lookup[key2] = j;
  arr[k].priority = priority;
  arr[k].data = data;
  arr[k].key = key1;
  lookup[key1] = k;
}

unsigned int size(PQ *pq) {
  return pq->first_available;
}

unsigned int capacity(PQ *pq) {
  return pq->capacity;
}

int less(unsigned int j, unsigned int k, Item arr[]) {
  return (arr[j].priority <= arr[k].priority);
}

void swim(unsigned int k, Item arr[], unsigned int lookup[]) {
  while (k > ROOT_IDX && less (k, PARENT(k), arr)) {
    exch(k, PARENT(k), arr, lookup);
    k = PARENT(k);
  }
}

void sink (unsigned int k, Item arr[], unsigned int first_available, unsigned int lookup[]) {
  while (LEFT_CHILD(k) < first_available) { /* Requirement that capacity <= MAX_SIZE be of reasonable size */
    unsigned j = LEFT_CHILD(k);
    if (j+1 < first_available && less(j+1, j, arr)) j++; /* careful with j+1 overflow? */
    if (less(k, j, arr)) break;
    exch(k, j, arr, lookup);
    k = j;
  }
}

void insert_nc(PQ *pq, Item *x) {
  pq->heap_cells[pq->first_available].priority = x->priority;
  pq->heap_cells[pq->first_available].data = x->data;
  swim(pq->first_available, pq->heap_cells, pq->key_table);
  pq->first_available++;
}

void remove_min_nc(PQ *pq, Item* item) {
  pq->first_available--;
  exch(ROOT_IDX, pq->first_available, pq->heap_cells, pq->key_table);
  item->priority = pq->heap_cells[pq->first_available].priority;
  item->data = pq->heap_cells[pq->first_available].data;
  sink(ROOT_IDX, pq->heap_cells, pq->first_available, pq->key_table);
}  

void insert(PQ *pq, Item *x) {
  if (pq->first_available == pq->capacity) return; /* Hrm, maybe should signal error or grow heap or whatever... */
  insert_nc(pq, x);
}

Item* remove_min(PQ *pq) {
  if (pq->first_available == ROOT_IDX) return 0;
  Item* item = (Item*) mallocN(sizeof(Item));
  remove_min_nc(pq, item);
  return item;
}

PQ* make() { /* could take a size parameter I suppose... */
  Item* arr = (Item*) mallocN(sizeof(Item) * INITIAL_SIZE);
  PQ *pq = (PQ*) mallocN(sizeof(PQ));
  pq->capacity = INITIAL_SIZE;
  pq->first_available = 0;
  pq->heap_cells = arr;
  return pq;
}

/* could imagine adding some additonal functions:
     heapify
     ?
*/

/*@ predicate insertion_point{L}(integer ip, int* a, integer from, integer to, int key) =
  @   from <= ip <= to &&
  @   (\forall integer i; from <= i < ip ==> \at(a[i], L) < key) &&
  @   (\forall integer i; ip <= i < to ==> key < \at(a[i], L));
  @*/

/*@ predicate sorted{L}(int* a, integer low, integer high) =
  @   \forall integer i; low <= i < high ==> \at(a[i], L) <= \at(a[i + 1], L);
  @*/

/*@ lemma mean_le:
  @   \forall integer i; 
  @   \forall integer j;
  @   i <= j ==> 
  @   i <= i + ((j - i) / 2) <= j;
  @*/

/*@ lemma sorted_array_index_elt_le{L}:
  @   \forall int* a;
  @   \forall integer from;
  @   \forall integer to;
  @     \valid(a+ (from..to - 1)) ==>
  @     sorted{L}(a, from, to - 1) ==>
  @     \forall integer i;
  @     \forall integer j;
  @       from <= i <= to - 1 ==>
  @       from <= j <= to - 1 ==>
  @       i <= j ==>
  @       a[i] <= a[j];
  @*/

/*@ lemma sorted_array_index_lt{L}:
  @   \forall int* a;
  @   \forall integer from;
  @   \forall integer to;
  @     \valid(a+ (from..to - 1)) ==>
  @     sorted{L}(a, from, to - 1) ==>
  @     \forall integer i;
  @     \forall integer j;
  @       from <= i <= to - 1 ==>
  @       from <= j <= to - 1 ==>
  @       a[i] < a[j] ==>
  @       i < j;
  @*/

/*@ requires 
  @   0 <= from && from <= to && to <= a.length && \valid(a+ (from..to - 1)) && sorted(a, from, to - 1);
  @ 
  @ assigns
  @   \nothing;
  @
  @ behavior has_key: 
  @   assumes
  @     \exists integer i; from <= i <= to - 1 && a[i] == key;
  @   ensures
  @     a[\result] == key;
  @
  @ behavior has_not_key:
  @   assumes 
  @     \forall integer i; from <= i <= to - 1 ==> a[i] != key;
  @   ensures
  @     insertion_point(-\result - 1, a, from, to, key);
  @
  @ disjoint behaviors;
  @
  @ complete behaviors;
  @
  @*/
int binary_search_range(int a[], int from, int to, int key) {
  int low = from;
  int high = to - 1;
  /*@ loop invariant 
    @   from <= low && high <= to - 1;
    @
    @ for has_key:
    @   loop invariant
    @     \exists integer i; low <= i <= high && a[i] == key; 
    @   
    @ for has_not_key:
    @   loop invariant 
    @     low <= len &&
    @     (\forall integer i; from <= i < low ==> a[i] < key) &&
    @     (\forall integer i; high < i <= to - 1 ==> key < a[i]);
    @     
    @ loop variant
    @   high - low;
    @*/
  while (low <= high) {
    int mid = low + ((high - low) / 2);
    int mid_val = a[mid];
    if (mid_val < key) {
      low = mid + 1;
    } else if (mid_val > key) {
      high = mid - 1;
    } else {
      return mid;
    }
  }
  return -low - 1;
}

int binary_search(int a[], int len, int key) {
  return binary_search_range(a, 0, len, key);
}

int four[4] = {1, 2, 3, 4};

int main() {
  int s = binary_search(four, 4, 3);
  return s;
}

/* Copyright (c) 2016 VMware, Inc. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at:
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef OVN_DATALOG_PRIV_H
#define OVN_DATALOG_PRIV_H 1

#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <stdint.h>
#include <inttypes.h>
#include <time.h>

#include "util.h"

/* --------------------------------------------------------------------------
 * CONSTANTS
 * --------------------------------------------------------------------------
 */

#define LOG_COMP            0     /* 0 for not enable logging */

#define SZ_INIT_BITSET      16    /* initial capacity of bitset */
#define SZ_INIT_ARRAY       16    /* initial capacity of array */
#define SZ_INIT_HASH        11    /* initial capacity of hash map */

#define LOG_TOKEN_SZ        512   /* max length of token or string literal */

/* ENTITY TYPES */

#define ENT_UNKNOWN     0
#define ENT_INT32       1
#define ENT_TST_INT32   2   /* for testing only */
#define ENT_STR         3   /* null terminated string */
#define ENT_VALUE       4   /* log_value_t* */
#define ENT_INT_TUPLE   5   /* log_int_tuple_t* */
#define ENT_TUPLE       6   /* log_tuple_t* */
#define ENT_TABLE       7   /* log_table_t* */
#define ENT_RULE        8   /* log_rule_t* */
#define ENT_RULE_SET    9   /* log_rule_set_t* */
#define ENT_LOG_ENG     0x0a/* log_engine_t* */
#define ENT_JOIN_PARAM  0x0b/* log_join_param_t* */

#define ENT_ARRAY       0x0f/* array */
#define ENT_MAP         0x0e/* map */
#define ENT_SET         0x0d/* set */
#define ENT_INDEX       0x0c/* index of tuple */
                            /* the collection type must be */
                            /* (ENT_UNKNOWN, ENT_UNKNOWN, ENT_INDEX) */
#define ENT_BITSET      0x10

#define KEY_TYPE(t)     ((t) & 0xff)
#define KEY_ID(id)      ((id))
#define VALUE_TYPE(t)   (((t) >> 8) & 0xff)
#define VALUE_ID(id)    ((id) << 8)
#define COLL_TYPE(t)    (((t) >> 16) & 0xff) /* collection type */
#define COLL_ID(id)     ((id) << 16)

#define MAP_INT32_VALUE (KEY_ID(ENT_INT32) | VALUE_ID(ENT_VALUE))

/* conversion between pointer and int32_t. type cast will produce warning */
#define ptr2i(v) ((int32_t)(((union { intptr_t i; void* p; })(v)).i))
#define i2ptr(v) (((union { intptr_t i; void* p; })(intptr_t)(v)).p)

#define TYPE(t, def)            t /* showing type of object in array, set */
#define TYPE2(t, key, val)      t /* showing type of object in map */

/* --------------------------------------------------------------------------
 * BITSET, ARRAY, HASH MAP, AND HASH SET
 * --------------------------------------------------------------------------
 */

/* when type is known for a collection, it could be freed using [coll]_free,
 * and all nested structure will be freed. items never cross reference by
 * default, except for log_values. when there is cross reference, the 'free'
 * function must be defined. 'global value' could be regarded as global
 * context for the object.
 *
 * naming convention for collection function: collection_method:
 * collection could be: bitset, array, set, map
 * method could be: (init, free), (add, del), (ins, rmv), (get, set).
 */

struct hash_s;

typedef struct meta_s {
    int32_t type;           /* must be the first field */
    bool alloc;             /* indicates if the structure is from malloc */
    struct hash_s* glb_values;
} meta_t;

typedef struct bitset_s {
    meta_t m;
    int32_t size;           /* size of items in bytes */
    int32_t len;            /* length of allocated items */
    uint32_t* items;
} bitset_t;

typedef struct array_s {
    meta_t m;
    void** item;
    int32_t size;           /* size of the array */
    int32_t len;            /* length of allocated space */
} array_t;

typedef struct map_node_s {
    struct map_node_s* next;
    void* key;
    void* value;
} map_node_t;

/* set_node_s, index_node_s must have the same structure as map_node_s
 * except the last field. assume they have the same alignment, and
 * map_node_s is used to access both.
 */
typedef struct set_node_s {
    struct set_node_s* next;
    void* key;
} set_node_t;

/* for index map, the aux points to log_int_tuple which defines the
 * index. the key of each entry points to one tuple of the tuple set
 * whose elements share the same tuple key. the set is represented by
 * double link presented in the tuple.
 */
typedef struct index_node_s {
    struct index_node_s* next;
    void* key;              /* points to one tuple of the set */
    int32_t hash_code;      /* hash_code of the tuple key */
} index_node_t;

typedef struct hash_s {
    meta_t m;
    map_node_t** bucket;
    int32_t size;           /* size of items */
    int32_t len;            /* length of bucket array */
    void* aux;              /* extra data */
} hash_t;

typedef hash_t map_t;
typedef hash_t set_t;

/* --------------------------------------------------------------------------
 * DATA STRUCTURE OF LOG ENGINE
 * --------------------------------------------------------------------------
 */

typedef struct log_config_s {
    char sep1;              /* field separator */
    char sep2;              /* record separator */
} log_config_t;

typedef struct log_value_s {/* variable size structure */
    int32_t hash_code;      /* must be first field */
    int32_t ref_no;         /* number of references */
    /* the actual size is abs(size) and it does not count terminating 0 */
    /* 0 is always padded no matter .a or .p is used for printf */
    int32_t size;           /* size < 0 indicates using value.p */
                            /* size >= 0 indicates using value.a */
    union {
        char a[0];          /* byte array, need not terminate with null */
        char* p;            /* only used in populating the value set */
    } value;
} log_value_t;

/*
 * log_tuple_s.indexes is a log_tuple_t pointer array, which represents
 * an array of double linked list. for index i, indexes[i * 2] points to
 * previous node and index[i * 2 + 1] points to success node.
 */
typedef struct log_tuple_s {/* variable size structure */
    /* do not have size due to memory consideration */
    int32_t hash_code;      /* must be first field */
    int32_t n_values;       /* duplicated, see table.num_fields */
    int64_t count;          /* valid only in table, when tuple is outside */
                            /* table, it has different meaning */
    struct log_tuple_s** indexes;  /* valid only in table */
    log_value_t* values[0]; /* field array of the tuple */
} log_tuple_t;

typedef struct log_int_tuple_s {/* variable size structure */
    int32_t hash_code;      /* must be first field */
    int32_t n_items;        /* number of integers */
    int32_t values[0];
} log_int_tuple_t;

struct log_engine_s;

/* index_map, index_def and tuple.indexes must have the same size,
 * and aligns to each other, i.e. assume there is N indexes defined,
 * tuple.indexes has N * 2 items, and index_map and index_def
 * has N items. For index j:
 * (1) index_def[key_def]->j, defines the index, e.g., '0:3:4'->1.
 * (2) index_map[j] defines hash map from key tuples to tuple set.
 *     The aux of this map points to corresponding index_def's key.
 * (3) tuple.indexes[j * 2] and tuple.indexes[j * 2 + 1] defines tuple set.
 */
typedef struct log_table_s {
    meta_t m;
    int32_t table_index;    /* id of the table */
    int32_t num_fields;     /* also present in each tuple */
    bool is_remove;         /* valid if this is delta */

    TYPE2(map_t, log_int_tuple_t*, int32_t) index_def;
    TYPE(array_t, hash_t*) index_map;
    TYPE(set_t, log_tuple_t*) tuples;
} log_table_t;

typedef struct log_rule_s {
    meta_t m;

    bool is_union;
    /*
     * table index start from 0. item 0 is left side
     * example X1 : X2, X3 -> 7, 3, 6
     * rule and param has the same sequence.
     */
    TYPE(array_t, int32_t) rule;

    /*
     * item 0 is left side. param index starts from 0.
     * example: X1(a,b) : X2(a, -), X3('c', b) -> ((0, 1), (0, -1), (-2, 1))
     * -1 indicates 'ignore', -2 is the index for first constant
     */
    TYPE(array_t, array_t*) param; /* array of array of integer */
    /* example: -2 -> 'c', map integer to value */
    TYPE2(map_t, int32_t, log_value_t*) const_param;

    /* example: 0->'a', 1->'b' */
    TYPE2(map_t, int32_t, log_value_t*) param_name_map;
} log_rule_t;

typedef struct log_rule_set_s {
    meta_t m;

    /* example: 7-> 'X1' */
    TYPE2(map_t, int32_t, log_value_t*) rule_name_map;
    TYPE2(map_t, log_value_t*, int32_t) rule_index_map;

    /* table index -> rule. table index starts from 0 */
    TYPE2(map_t, int32_t, log_rule_s*) rules;
    /* table index -> table index set */
    TYPE2(map_t, int32_t, array_t*) table_rule_map; /* array of integer */
    /* example: 3->(7), 6->(7), list is ordered */

    TYPE(set_t, int32_t) input_tables;
    TYPE(set_t, int32_t) output_tables;
    TYPE2(map_t, int32_t, int32_t) param_size;
} log_rule_set_t;

typedef struct log_io_s {
    TYPE(array_t*, log_table_t*) inp_remove;
    TYPE(array_t*, log_table_t*) inp_insert;
    TYPE(array_t*, log_table_t*) res;

    log_table_t* cur_tbl;
    log_tuple_t* cur_tuple;
    int32_t t_idx;          /* table index */
    int32_t f_idx;          /* field index */

    map_node_t* hash_node;  /* current node of iterator */
    int32_t hash_b;         /* current bucket of iterator */
} log_io_t;

typedef struct log_engine_s {
    meta_t m;

    log_rule_set_t rule_set;
    /* map table index to log_table_t */
    TYPE2(map_t, int32_t, log_table_t*) tables;

    bool (*ext_func)( /* to reset state if last 3 param are NULL */
        struct log_engine_s* eng, log_table_t*, log_table_t*, log_table_t*);

    log_io_t io; /* temporary data for calling (put|get)_(table|field) */
} log_engine_t;

typedef struct log_join_param_s {
    meta_t m;

    log_int_tuple_t*            index2;
    TYPE(array_t, log_value_t*) select1;
    TYPE(array_t, int32_t)      select1i; /* match select1 in size */
    TYPE(array_t, int32_t)      rem1;
    TYPE(array_t, int32_t)      rem2;
    TYPE(array_t, int32_t)      out_param;
    bool full_join;
} log_join_param_t;

/* --------------------------------------------------------------------------
 * PROTOTYPES
 * --------------------------------------------------------------------------
 */

void        log_topo_sort(
                    TYPE2(map_t*, log_value_t*, set_t*) g, /* set of value */
                    TYPE(array_t*, log_value_t*) order,
                    TYPE(set_t*, log_value_t*) in_nodes,
                    TYPE(set_t*, log_value_t*) out_nodes);
void        log_sort_array(
                    int start, array_t* list, array_t* sem1, array_t* sem2);
int         log_insert_item(
                    int val, array_t* list, void* obj1,
                    void* obj2, array_t* sem1, array_t* sem2);

void        log_set_sep(char sep1, char sep2);
void        log_set_global_value(set_t* s);

void        log_sync_init(const char* log, set_t* gv);
void        log_sync_parse(map_t* sem);
void        log_sem_process(log_rule_set_t* rule_set, map_t* sem);
void        log_eng_set_ext_func(log_engine_t* eng, void* func);
log_engine_t* log_eng_parse(const char* rules, set_t* gv);

int32_t     log_hash_code(hash_t* m, const void* v);
int32_t     log_hash_code_byte(const void* v, int32_t* size);
bool        log_key_equal(hash_t* m, const void* k1, const void* k2);
void        log_coll_free(void* coll, int32_t type, set_t* gv);

map_t*      log_hash_init(map_t* m, int type, int sz_init, hash_t*);
void        log_hash_free(hash_t*);
void        log_hash_add(map_t* m, void* k, void* v);
void*       log_hash_del(map_t* m, void* k);
void        log_hash_rehash(map_t* m);
bool        log_hash_next(map_t* m, int32_t* b, map_node_t** cur);
void*       log_hash_get_one(map_t* m);

bitset_t*   log_bitset_init(bitset_t* set);
void        log_bitset_free(bitset_t*);

array_t*    log_array_init(
                    array_t* a, int32_t type, int32_t i_size, set_t* gv);
void        log_array_free(array_t*);
array_t*    log_array_clone(array_t* a);
int32_t     log_array_look_for(array_t* a, void* v);

log_value_t*        log_value_init(const char* v, int32_t size, set_t* gv);
log_int_tuple_t*    log_int_tuple_init(TYPE(array_t*, int32_t) a);
void                log_int_tuple_free(log_int_tuple_t*);

log_tuple_t*        log_tuple_init(int32_t n_values);
void                log_tuple_free(log_tuple_t*, set_t*, bool);
log_tuple_t*        log_tuple_init_val(log_value_t** val, int32_t n_values);
log_tuple_t*        log_tuple_init_str(const char* t, char sep, set_t* gv);
log_tuple_t*        log_tuple_init_str_null(
                        const char* t, char sep, set_t* gv);

log_table_t*        log_table_init(
                        log_table_t* tbl, int32_t n, int32_t f,
                        int32_t size, set_t* gv);
void                log_table_free(log_table_t* tbl);
void                log_table_add(log_table_t* tbl, log_tuple_t* t);
void                log_table_remove(log_table_t* tbl, log_tuple_t* t);

int32_t             log_table_add_index(
                        log_table_t* tbl, log_int_tuple_t* index_key);
log_tuple_t*        log_index_get_index(
                        log_table_t* tbl, log_tuple_t* t, int32_t i_idx);

void                log_rule_free(log_rule_t* rule);
void                log_rule_set_init(log_rule_set_t* rs, set_t* gv);
void                log_rule_set_free(log_rule_set_t*);

log_engine_t*       log_engine_init(log_engine_t* log, set_t* gv);
void                log_engine_free(log_engine_t*);

log_join_param_t*   log_join_param_init(
                        log_join_param_t* jp, log_int_tuple_t* i2, set_t* gv);
void                log_join_param_free(log_join_param_t*);

log_table_t*        log_tblopr_join(
                        log_table_t* t1, log_table_t* t2,
                        log_join_param_t* joinp);
void                log_eng_do_join(
                        log_engine_t* eng,
                        log_table_t* input, log_table_t* output);
void                log_eng_do_union(log_engine_t* eng,
                        log_table_t* input, log_table_t* output);

TYPE(array_t*, log_table_t*) log_eng_delta(
                        log_engine_t* eng,
                        TYPE(array_t*, log_table_t*) inp_remove,
                        TYPE(array_t*, log_table_t*) inp_insert);
TYPE(array_t*, log_table_t*) log_eng_query(
                        log_engine_t* eng,
                        TYPE(array_t*, log_table_t*) input);

log_table_t*        log_get_table(log_engine_t* eng, const char* name);
log_table_t*        log_get_org_table(log_engine_t* eng, log_table_t* t);
log_tuple_t*        log_query_on0(log_engine_t* eng,
                        int32_t tid, log_value_t* value);

log_table_t*        log_io_table_name_reset(
                        log_engine_t* eng, const char* name);
bool                log_io_parse_line(
                        const char* line, log_engine_t* eng, bool use_null,
                        TYPE(array_t*, log_table_t*) inp_remove,
                        TYPE(array_t*, log_table_t*) inp_insert);
int32_t             log_io_gen_line(char* text, int pos, log_engine_t* eng,
                         TYPE(array_t*, log_table_t*) all);

int32_t log_coll_print(
            char* buf, int32_t pos, void* item, int32_t type, bool verbose);
int32_t log_array_print(char* buf, int32_t pos, array_t* a, bool verbose);
int32_t log_hash_print(char* buf, int32_t pos, hash_t* m, bool verbose);
int32_t log_table_print(char* buf, int32_t pos, log_table_t* t, bool verbose);
int32_t log_index_print(char* buf, int32_t pos, log_table_t* t);
int32_t log_tuple_print(char* buf, int32_t pos, log_tuple_t* t);
int32_t log_rule_set_print(char* buf, int32_t pos, log_rule_set_t* rs);

/* --------------------------------------------------------------------------
 * MACROS AND INLINE IMPLEMENTATIONS
 * --------------------------------------------------------------------------
 */

#define map_size(m)     ((m)->size)
#define map_has(m, k)   (log_hash_get(m, k) != NULL)
#define map_free(m)     log_hash_free(m)
#define map_del(m, k)   log_hash_del(m, k)

#define set_size(m)     ((m)->size)
#define set_has(m, k)   (log_hash_get(m, k) != NULL)
#define set_free(m)     log_hash_free(m)
#define set_del(m, k)   log_hash_del(m, k)

#define array_size(a)   ((a)->size)
#define table_size(t)   (set_size(&(t)->tuples))

#define map_get_int(m, k)           ptr2i(map_get(m, k))
#define array_get_int(a, i)         ptr2i(array_get(a, i))

#define log_index_i_pre(tuple, i)   ((tuple)->indexes[(i) * 2])
#define log_index_i_suc(tuple, i)   ((tuple)->indexes[(i) * 2 + 1])

/* --------------------------------------------------------------------------
 * META DATA
 * --------------------------------------------------------------------------
 */

static inline void*
c_realloc(void* ptr, size_t old_sz, size_t new_sz)
{
    /* ptr could be NULL and expanded area will be zeroed */
    void* n = realloc(ptr, new_sz);
    memset(((char*)n) + old_sz, 0, new_sz - old_sz);
    return n;
}

static inline void
hash_code_array_init(int32_t* c)
{
    /* sequence of 0 will have different hash code depending on its length */
    *c = 1;
}

static inline void
hash_code_array_add(int32_t* c, int32_t i)
{
    *c = (*c) * 31 + i;
}

static inline void
hash_code_array_final(int32_t* c)
{
    if (*c < 0) *c = -(*c);
}

static inline void
coll_alloc(void* ptr, int32_t size, int32_t type, void* global_values)
{
    meta_t** m = (meta_t**)ptr;
    if (*m == NULL) {
        *m = malloc(size);
        (*m)->alloc = true;
    }
    else {
        (*m)->alloc = false;
    }

    (*m)->type = COLL_ID(type);
    (*m)->glb_values = global_values;
}

static inline void
coll_free_ptr(void* ptr)
{
    meta_t* m = ptr;
    if (m->alloc) free(m);
}

static inline void
log_value_ref(log_value_t* v)
{
    v->ref_no++;
}

static inline void
log_value_free(log_value_t* v, set_t* gv)
{
    if (v->ref_no > 1) --v->ref_no;
    else {
        int32_t sv_type = gv->m.type;
        gv->m.type = 0;
        log_hash_del(gv, v);
        gv->m.type = sv_type;
        free(v);
    }
}

static inline void
check_value_ref(void* v, int32_t type, set_t* gv, bool add)
{
    if (v == NULL) return;
    if (!add) log_coll_free(v, type, gv);
    else if (type == ENT_VALUE) log_value_ref((log_value_t*)v);
}

/* --------------------------------------------------------------------------
 * BITSET
 * --------------------------------------------------------------------------
 */

static inline void
bitset_resize(bitset_t* set, int32_t len)
{
    /* since there is no reset operation, it always expands */
    set->items = c_realloc(set->items,
        set->len * sizeof(int32_t), len * sizeof(int32_t));
    /* assume align to 4 bytes for int32_t */
    set->len = len;
}

static inline void
bitset_set(bitset_t* set, int32_t b)
{
    int32_t p = b >> 5;
    if (p >= set->size) {
        set->size = p + 1;
        if (set->size > set->len) bitset_resize(set, set->size);
    }

    set->items[p] |= 1 << (b % 32);
}

static inline bool
bitset_get(bitset_t* set, int b)
{
    int p = b >> 5;
    if (p >= set->size) return false;
    return (set->items[p] & (1 << (b % 32))) != 0;
}

static inline bool
bitset_empty(bitset_t* set)
{
    int i;
    for (i = 0;i < set->size;i++)
        if (set->items[i] != 0) return false;
    return true;
}

static inline void
bitset_and(bitset_t* dest, bitset_t* src)
{

    int32_t m_size = dest->size > src->size ? src->size : dest->size;

    int i;
    for (i = 0;i < m_size;i++) dest->items[i] &= src->items[i];
    for (i = m_size;i < dest->size;i++) dest->items[i] = 0;
}

/* --------------------------------------------------------------------------
 * ARRAY
 * --------------------------------------------------------------------------
 */

static inline void
array_add(array_t* a, void* i)
{
    ovs_assert(a->size <= a->len);

    if (a->size == a->len) {
        a->item = c_realloc(a->item,
            a->len * sizeof(void*), a->len * 2 * sizeof(void*));
        a->len = a->len * 2;
    }
    a->item[a->size++] = i;
    check_value_ref(i, KEY_TYPE(a->m.type), a->m.glb_values, true);
}

static inline void
array_ins(array_t* a, int32_t pos, void* i)
{
    array_add(a, NULL); /* make room for new item */
    memmove(&a->item[pos + 1], &a->item[pos],
        (a->size - pos - 1) * sizeof(void*)); /* size has increased by 1 */

    a->item[pos] = i;
    check_value_ref(i, KEY_TYPE(a->m.type), a->m.glb_values, true);
}

static inline void*
array_rmv(array_t* a, int32_t pos)
{
    /* no change to ref */
    void* org = a->item[pos];
    memmove(&a->item[pos], &a->item[pos + 1],
        (a->size - pos - 1) * sizeof(void*));
    a->size--;
    return org;
}

static inline void*
array_get(array_t* a, int32_t i)
{
    ovs_assert(i >= 0 && i < a->size);
    return a->item[i];
}

static inline void
array_set(array_t* a, int i, void* v)
{
    ovs_assert(i >= 0 && i < a->size);
    check_value_ref(a->item[i], KEY_TYPE(a->m.type), a->m.glb_values, false);

    a->item[i] = v;
    check_value_ref(v, KEY_TYPE(a->m.type), a->m.glb_values, true);
}

/* --------------------------------------------------------------------------
 * HASH TABLE
 * --------------------------------------------------------------------------
 */

static inline map_node_t*
log_hash_get(map_t* m, void* k)
{
    /* no change to reference count */

    int32_t code = log_hash_code(m, k);
    int32_t slot = code % m->len;
    map_node_t* head = m->bucket[slot];

    while (head != NULL) {
        if (log_key_equal(m, head->key, k)) return head;
        head = head->next;
    }
    return NULL;
}

/* --------------------------------------------------------------------------
 * MAP
 * --------------------------------------------------------------------------
 */

static inline map_t*
map_init(map_t* m, int type, int sz_init, set_t* gv)
{
    return log_hash_init(m, type | COLL_ID(ENT_MAP), sz_init, gv);
}

static inline void*
map_get(map_t* m, void* k)
{
    map_node_t* node = log_hash_get(m, k);
    if (node == NULL) return NULL;
    else return node->value;
}

static inline void
map_add(map_t* m, void* k, void* v)
{
    map_node_t* node = log_hash_get(m, k);

    if (node != NULL) {
        void* old = node->value;
        check_value_ref(old, VALUE_ID(m->m.type), m->m.glb_values, false);

        node->value = v;
        check_value_ref(v, VALUE_ID(m->m.type), m->m.glb_values, true);

    } else log_hash_add(m, k, v);
}

/* --------------------------------------------------------------------------
 * SET
 * --------------------------------------------------------------------------
 */

static inline set_t*
set_init(set_t* m, int type, int sz_init, set_t* gv)
{
    return log_hash_init(m, type | COLL_ID(ENT_SET), sz_init, gv);
}

static inline void*
set_get(set_t* m, void* k)
{
    map_node_t* node = log_hash_get(m, k);
    if (node == NULL) return NULL;
    else return node->key;
}

static inline void
set_add(set_t* m, void* k)
{
    map_node_t* node = log_hash_get(m, k);
    if (node != NULL) return;
    log_hash_add(m, k, NULL);
}

/* --------------------------------------------------------------------------
 * ITERATIONS
 * --------------------------------------------------------------------------
 */

/* nested usage is supported.
 * 'continue' does not work with set.
 * 'if (c) [TYPE]_EXIT; else {}' does not work with map and set.
 */

#define ARRAY_ALL_0(array, node, type, typec)                   \
    {   int __array_i = 0;                                      \
        for (;__array_i < (array)->size;__array_i++) {          \
            type node = typec((array)->item[__array_i]); {

#define ARRAY_EXIT break
#define ARRAY_END }}}

#define MAP_ALL(map, node)                                      \
    {   bool __map_exit = false;                                \
        map_t* __map = (map_t*)(map);                           \
        int __map_i = 0;                                        \
        for (;__map_i < __map->len;__map_i++) {                 \
        if (__map_exit) break;                                  \
        struct map_node_s* __map_head = __map->bucket[__map_i]; \
        while (__map_head != NULL) {                            \
            struct map_node_s* node = __map_head;               \
            __map_head = __map_head->next; {

#define MAP_EXIT {__map_exit = true; break; }
#define MAP_END }}}}

#define SET_ALL_0(set, node, type, typec)                       \
    {   bool __set_exit = false, __set_rmv;                     \
        struct set_node_s* __set_save = NULL, *__set_pre;       \
        set_t* __set = (set_t*)(set);                           \
        int32_t __set_i = 0;                                    \
        for (;__set_i < __set->len;__set_i++) {                 \
        if (__set_exit) break;                                  \
        struct set_node_s* __set_this = (struct set_node_s*)    \
                                      (__set->bucket[__set_i]); \
        __set_pre = NULL;                                       \
        while (__set_this != NULL) {                            \
            type node = typec(__set_this->key);                 \
            __set_rmv = false; {

#define SET_REMOVE_ITEM /* will not rehash */                   \
    (__set_rmv = true, __set->size--, __set_save = __set_this,  \
    __set_pre == NULL ? (__set->bucket[__set_i] =               \
    (map_node_t*)__set_this->next) :                            \
    (map_node_t*)(__set_pre->next = __set_this->next),          \
    __set_this = __set_this->next, free(__set_save))

#define SET_EXIT {__set_exit = true; break; }

#define SET_END }                                               \
    if (!__set_rmv) { __set_pre = __set_this;                   \
    __set_this = __set_this->next;} }}                          \
    __set_save++; __set_pre++; } /* make no warning */

#define INDEX_ALL(tuple, i_idx, node)                           \
    {   bool __index_first = true;                              \
        log_tuple_t* __index_head = tuple;                      \
        log_tuple_t* node;                                      \
        if (__index_head != NULL) { for (;;) {                  \
            if (__index_first) {                                \
                node = __index_head; __index_first = false; }   \
            else {                                              \
                (node) = (node)->indexes[i_idx * 2 + 1];        \
                if (__index_head == node) break;                \
            }

#define INDEX_EXIT break
#define INDEX_END }}}

#define ARRAY_ALL(array, node, type) ARRAY_ALL_0(array, node, type, (type))
#define ARRAY_ALL_INT(array, node)   ARRAY_ALL_0(array, node, int32_t, ptr2i)

#define SET_ALL(set, node, type)     SET_ALL_0(set, node, type, (type))
#define SET_ALL_INT(set, node)       SET_ALL_0(set, node, int32_t, ptr2i)

#endif /* datalog-private.h */

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

#include <config.h>
#include "datalog.h"
#include "datalog-private.h"

/* ==========================================================================
 * BASIC COLLECTIONS
 * ==========================================================================
 */

void
log_coll_free(void* coll, int32_t type, set_t* gv)
{
    switch (type) {
    case ENT_BITSET:    log_bitset_free(coll); break;
    case ENT_ARRAY:     log_array_free(coll); break;

    case ENT_MAP:
    case ENT_SET:
    case ENT_INDEX:     log_hash_free(coll); break;

    case ENT_TUPLE:     log_tuple_free(coll, gv, true); break;
    case ENT_VALUE:     log_value_free(coll, gv); break;
    case ENT_TABLE:     log_table_free(coll); break;
    case ENT_INT_TUPLE: log_int_tuple_free(coll); break;
    case ENT_RULE:      log_rule_free(coll); break;
    case ENT_RULE_SET:  log_rule_set_free(coll); break;
    case ENT_LOG_ENG:   log_engine_free(coll); break;
    case ENT_JOIN_PARAM:log_join_param_free(coll); break;
    }
}

/* --------------------------------------------------------------------------
 * BITSET
 * --------------------------------------------------------------------------
 */

bitset_t*
log_bitset_init(bitset_t* set)
{
    coll_alloc(&set, sizeof(bitset_t), ENT_BITSET, NULL);
    set->len = SZ_INIT_BITSET;
    set->items = calloc(set->len, sizeof(void*));
    set->size = 0;
    return set;
}

void
log_bitset_free(bitset_t* dest)
{
    if (dest->items != NULL) free(dest->items);
    coll_free_ptr(dest);
}

/* --------------------------------------------------------------------------
 * ARRAY
 * --------------------------------------------------------------------------
 */

void
log_set_global_value(set_t* s)
{
    s->m.type = KEY_ID(ENT_VALUE) | COLL_ID(ENT_SET);
    s->m.glb_values = s;
}

array_t*
log_array_init(array_t* a, int32_t type, int32_t i_size, set_t* gv)
{
    coll_alloc(&a, sizeof(array_t), ENT_ARRAY, gv);

    a->len = i_size;
    a->m.type |= type;
    if (a->len == 0) a->len = SZ_INIT_ARRAY;
    a->item = calloc(a->len, sizeof(void*));
    a->size = 0;
    return a;
}

array_t*
log_array_clone(array_t* a)
{
    int i;
    array_t* na = log_array_init(NULL, a->m.type, a->size, a->m.glb_values);
    memcpy(na->item, a->item, a->size * sizeof(void*));
    na->size = a->size;

    for (i = 0;i < a->size;i++)
        check_value_ref(na->item[i], KEY_TYPE(na->m.type),
                        na->m.glb_values, true);
    return na;
}

void
log_array_free(array_t* a)
{
    int i;
    for (i = 0;i < a->size;i++)
        check_value_ref(a->item[i], KEY_TYPE(a->m.type),
                        a->m.glb_values, false);
    free(a->item);
    coll_free_ptr(a);
}

int32_t
log_array_look_for(array_t* a, void* v)
{
    int i = 0;
    bool found = false;

    ARRAY_ALL(a, item, const void*)
        if (item == v) {
            found = true;
            ARRAY_EXIT;
        }
        i++;
    ARRAY_END

    if (found) return i;
    else return -1;
}

int32_t
log_array_print(char* buf, int32_t pos, array_t* a, _Bool verbose) {
    int i = 0;
    buf[pos++] = '[';
    int32_t ktype = KEY_TYPE(a->m.type);
    for (i = 0; i < a->size; i++) {
        if (i > 0)
            buf[pos++] = ',';

        pos = log_coll_print(buf, pos, a->item[i], ktype, verbose);
    }
    buf[pos++] = ']';
    return pos;
}

/* --------------------------------------------------------------------------
 * HASH CODE
 * --------------------------------------------------------------------------
 */

int32_t
log_hash_code_byte(const void* v, int32_t* size)
{
    /*
     * size of 0 indicates null terminated string, and actual size not
     * including null is returned in size.
     */

    const unsigned char* p = v;
    uint32_t hash = 0;
    int32_t i = 0;

    /* Jenkins's Hash */
    if (*size == 0) {
        unsigned char c;
        while ((c = *p++) != 0) {
            i++;
            hash += c;
            hash += (hash << 10);
            hash ^= (hash >> 6);
        }
        *size = i;
    }
    else {
        int32_t s = *size;
        for (;i < s;i++) {
            hash += *p++;
            hash += (hash << 10);
            hash ^= (hash >> 6);
        }
    }

    hash += (hash << 3);
    hash ^= (hash >> 11);
    hash += (hash << 15);
    return (int32_t) hash < 0 ? -hash : hash;
}

bool
log_key_equal(hash_t* m, const void* k1, const void* k2)
{
    /* if only one key is from hash_table, it must be k1 */
    int type = KEY_TYPE(m->m.type);

    if (type == ENT_VALUE) {
        return k1 == k2;
    }
    else if  (type == ENT_TUPLE) {
        const log_tuple_t* t1 = k1;
        const log_tuple_t* t2 = k2;

        if (t1->hash_code != t2->hash_code) return false;
        int32_t sz_tuples =
            (((log_table_t*)(m->aux))->num_fields) * sizeof(void*);
        return memcmp(&t1->values, &t2->values, sz_tuples) == 0;
    }

    else if (COLL_TYPE(m->m.type) == ENT_INDEX) {
        const log_tuple_t* t1 = k1;
        const log_tuple_t* t2 = k2;

        int i;
        log_int_tuple_t* index_def = m->aux;

        if (t1 == t2) return true;
        if (t2->count == 0) { /* compact form */
            for (i = 0;i < index_def->n_items;i++)
                if (t1->values[index_def->values[i]] != t2->values[i])
                    return false;
        }
        else {
            for (i = 0;i < index_def->n_items;i++)
                if (t1->values[index_def->values[i]] !=
                    t2->values[index_def->values[i]]) {
                    return false;
                }
        }
        return true;
    }

    else if (m == m->m.glb_values) {
        const log_value_t* v1 = k1;
        const log_value_t* v2 = k2;

        if (v1->size >= 0 && v2->size >= 0) return k1 == k2;
        if (v1->hash_code != v2->hash_code) return false;
        if (v1->size == 0 && v2->size == 0) return true;

        const void* p1 = v1->size > 0 ? v1->value.a : v1->value.p;
        const void* p2 = v2->size > 0 ? v2->value.a : v2->value.p;

        int32_t s1 = v1->size > 0 ? v1->size : (-v1->size);
        int32_t s2 = v2->size > 0 ? v2->size : (-v2->size);
        if (s1 != s2) return false;
        return memcmp(p1, p2, s1) == 0;
    }

    else if (type == ENT_INT_TUPLE) {
        const log_int_tuple_t* t1 = k1;
        const log_int_tuple_t* t2 = k2;

        if (t1->hash_code != t2->hash_code) return false;
        if (t1->n_items != t2->n_items) return false;

        int s = t1->n_items * sizeof(int32_t);
        return memcmp(&t1->values, &t2->values, s) == 0;
    }


    else if (type == ENT_INT32 || type == ENT_TST_INT32)
        return ptr2i((void*)k1) == ptr2i((void*)k2);
    else if (type == ENT_STR) return strcmp(k1, k2) == 0;

    ovs_assert(false);
    return false;
}

int32_t
log_hash_code(hash_t* m, const void* v)
{

    int32_t type = KEY_TYPE(m->m.type);
    if (type == ENT_STR) {
        int32_t size0 = 0;
        return log_hash_code_byte(v, &size0);
    }

    else if (COLL_TYPE(m->m.type) == ENT_INDEX) {
        int32_t i, code;
        log_tuple_t* t = (log_tuple_t*)v;

        log_int_tuple_t* index_def = m->aux;
        hash_code_array_init(&code);

        if (t->count == 0) { /* compact form */
            for (i = 0; i < index_def->n_items; i++) {
                log_value_t* v = t->values[i];
                hash_code_array_add(&code, v->hash_code);
            }
        } else {
            for (i = 0; i < index_def->n_items; i++) {
                log_value_t* v = t->values[index_def->values[i]];
                hash_code_array_add(&code, v->hash_code);
            }
        }

        hash_code_array_final(&code);
        return code;
    }

    else if (type == ENT_INT32) {
        int32_t n = ptr2i((void*)v);
        if (n < 0)
            n = -n;
        return n;
    } else if (type == ENT_TST_INT32)
        return ptr2i((void*)v) % 100;
    else
        return *(const int32_t*) v;
}

/* --------------------------------------------------------------------------
 * HASH TABLE
 * --------------------------------------------------------------------------
 */

map_t*
log_hash_init(map_t* m, int type, int sz_init, struct hash_s* values)
{
    coll_alloc(&m, sizeof(map_t), 0, values);
    m->m.type = type;
    m->size = 0;
    m->aux = NULL;
    m->len = sz_init == 0 ? SZ_INIT_HASH : sz_init;
    m->bucket = calloc(m->len, sizeof(void*));
    return m;
}

void
log_hash_free(map_t* m)
{
    int i;
    int32_t k_type = KEY_TYPE(m->m.type);
    int32_t v_type = VALUE_TYPE(m->m.type);
    int32_t c_type = COLL_TYPE(m->m.type);

    for (i = 0;i < m->len;i++) {
        map_node_t* head = m->bucket[i];
        while (head != NULL) {
            if (m == m->m.glb_values) free((void*)head->key);
            else {
                void* key = c_type != ENT_INDEX ? head->key : NULL;
                void* value = c_type == ENT_MAP ? head->value : NULL;
                check_value_ref(key, k_type, m->m.glb_values, false);
                check_value_ref(value, v_type, m->m.glb_values, false);
            }

            map_node_t* next = head->next;
            free(head);
            head = next;
        }
    }
    free(m->bucket);
    coll_free_ptr(m);
}

void
log_hash_rehash(map_t* m)
{
    int nlen;
    if (m->size > m->len * 2 / 3) nlen = m->len * 2;
    else if (m->size < m->len / 5 && m->size > 50) nlen = m->len / 2;
    else return; /* 50 is arbitrary number */

    int i;
    map_node_t** nb = calloc(nlen, sizeof(void*));

    for (i = 0;i < m->len;i++) {
        map_node_t* head = m->bucket[i];
        while (head != NULL) {
            map_node_t* next = head->next;

            int b;
            if (COLL_TYPE(m->m.type) == ENT_INDEX)
                b = ptr2i(head->value);
            else b = log_hash_code(m, head->key);

            /* the list is reversed in some sense */
            map_node_t* nhead = nb[b % nlen];
            if (nhead == NULL) head->next = NULL;
            else head->next = nhead;

            nb[b % nlen] = head;
            head = next;
        }
    }

    free(m->bucket);
    m->bucket = nb;
    m->len = nlen;
}

bool
log_hash_next(map_t* m, int32_t* b, map_node_t** cur)
{
    /* return false if there is no next */
    int32_t i = *b;
    for (;;) {
        if (*cur == NULL) {
            while (i < m->len && m->bucket[i] == NULL)
                i++;
            if (i >= m->len)
                return false;

            *b = i;
            *cur = m->bucket[i];
            return true;
        }
        *cur = (*cur)->next;
        if (*cur != NULL)
            return true;
        i++;
    }
    return false; /* never reach here */
}

void
log_hash_add(map_t* m, void* k, void* v)
{
    /* check key existence before calling this */

    int32_t type = COLL_TYPE(m->m.type);
    int32_t code = log_hash_code(m, k);
    int32_t slot = code % m->len;

    map_node_t* head = m->bucket[slot];
    map_node_t* item;

    if (type == ENT_MAP) {
        item = malloc(sizeof (map_node_t));
        item->value = v;
    }
    else if (type == ENT_SET) {
        item = malloc(sizeof (set_node_t));
    }
    else if (type == ENT_INDEX) {
        item = malloc(sizeof (index_node_t));
        item->value = i2ptr(code);
    }
    else ovs_assert(false);

    item->key = k;
    item->next = head;
    m->bucket[slot] = item;
    m->size++;

    check_value_ref(k, KEY_TYPE(m->m.type), m->m.glb_values, true);
    check_value_ref(v, VALUE_TYPE(m->m.type), m->m.glb_values, true);
    log_hash_rehash(m);
}

void*
log_hash_del(map_t* m, void* k)
{
    /* reference counter of value will NOT be changed, key is freed. */
    int32_t slot = log_hash_code(m, k) % m->len;

    map_node_t* head = m->bucket[slot];
    map_node_t* pre = NULL;

    while (head != NULL) {
        if (log_key_equal(m, head->key, k)) {
            if (pre == NULL) m->bucket[slot] = head->next;
            else pre->next = head->next;

            const void* value = COLL_TYPE(m->m.type) == ENT_MAP ?
                head->value : NULL;
            free(head);

            check_value_ref(k, KEY_TYPE(m->m.type), m->m.glb_values, false);
            /* value ref not changed, so that caller may still use
             * value, even only for free.
             */
            m->size--;
            log_hash_rehash(m);
            return (void*)value;
        }
        pre = head;
        head = head->next;
    }
    return NULL;
}

void*
log_hash_get_one(map_t* m)
{
    if (m->size == 0) return NULL;
    MAP_ALL(m, node)
        return node->key;
    MAP_END
    return NULL; /* not reachable */
}

int32_t
log_hash_print(char* buf, int32_t pos, hash_t* m, bool verbose)
{
    int i, j = 0;
    int32_t ktype = KEY_TYPE(m->m.type);
    int32_t vtype = VALUE_TYPE(m->m.type);
    int32_t htype = COLL_TYPE(m->m.type);

    if (verbose)
        pos += sprintf(buf + pos, "  hash %s, size=%d, len=%d\n",
                       htype == ENT_SET ? "set" : "map", m->size, m->len);
    else buf[pos++] = '{';

    for (i = 0;i < m->len;i++) {
        map_node_t* head = m->bucket[i];
        if (head == NULL) continue;
        if (verbose) pos += sprintf(buf + pos, "  [%d] ", i);

        while (head != NULL) {
            if (j > 0 && !verbose) buf[pos++] = ',';
            if (verbose)
                pos += sprintf(buf + pos, " (%x)",
                               log_hash_code(m, head->key));

            pos = log_coll_print(buf, pos, head->key, ktype, verbose);
            if (htype == ENT_MAP) {
                pos += sprintf(buf + pos, "->");
                pos = log_coll_print(buf, pos, head->value, vtype, verbose);
            }

            head = head->next;
            if (++j > 200) {
                pos += sprintf(buf + pos, " ...");
                if (verbose) pos += sprintf(buf + pos, "\n");
                return pos;
            }
        }
        if (verbose) pos += sprintf(buf + pos, "\n");
    }

    if (!verbose) buf[pos++] = '}';
    return pos;
}

/* ==========================================================================
 * LOG VALUES, INDEXES, AND TABLES
 * ==========================================================================
 */

/*
 * for tuple used as key passed to hash_* function, tuple->count:
 * == 0 indicates compact form, i.e., tuple only contains key fields, and
 *      hash_code has not been provisioned.
 * != 0 indicates tuple from table and hash_code is not the hash code
 *      for the key fields (is the hash code for tuple)
 */

log_int_tuple_t*
log_int_tuple_init(TYPE(array_t*, int32_t) a)
{
    log_int_tuple_t* it = calloc(1,
        sizeof(log_int_tuple_t) + sizeof(int32_t) * array_size(a));
    it->n_items = array_size(a);

    int32_t code;
    hash_code_array_init(&code);
    int i = 0;

    ARRAY_ALL_INT(a, v)
        it->values[i++] = v;
        hash_code_array_add(&code, v);
    ARRAY_END

    hash_code_array_final(&code);
    it->hash_code = code;
    return it;
}

static log_int_tuple_t*
log_int_tuple_clone(log_int_tuple_t* i)
{
    int32_t sz = sizeof(log_int_tuple_t) + sizeof(int32_t) * i->n_items;
    log_int_tuple_t* it = calloc(1, sz);
    memcpy(it, i, sz);
    return it;
}

void
log_int_tuple_free(log_int_tuple_t* t)
{
    free(t);
}

static int32_t
log_int_tuple_print(char* buf, int32_t pos, log_int_tuple_t* t)
{
    int i;
    buf[pos++] = '[';
    for (i = 0;i < t->n_items;i++) {
        if (i > 0) buf[pos++] = ',';
        pos += sprintf(buf + pos, "%d", t->values[i]);
    }
    buf[pos++] = ']';
    return pos;
}

log_value_t*
log_value_init(const char* v, int32_t size, set_t* gv)
{
    /* two types of values: null terminating string (size == 0)
     * and byte array (size indicates the size of byte array)
     * data will be copied and saved in global value set.
     * the ref_no is increased after calling this.
     */

    log_value_t inp;
    inp.value.p = (char*)v;
    inp.size = size;
    inp.hash_code = log_hash_code_byte(v, &inp.size);
    inp.size = -inp.size; /* using value.p */

    int32_t sv_type = gv->m.type;
    gv->m.type = 0;

    log_value_t* setv = set_get(gv, &inp);
    gv->m.type = sv_type;

    if (setv != NULL) {
        setv->ref_no++;
        return setv;
    }

    inp.size = -inp.size;
    int32_t offset = inp.value.a - ((char*)&inp);
    setv = calloc(1, offset + inp.size + 1);
    memcpy(setv, &inp, offset);

    memcpy(setv->value.a, v, inp.size);
    /* make it null terminate for printing when debugging */
    *((char*)setv->value.a + inp.size) = 0;

    setv->ref_no = 0;
    log_hash_add(gv, setv, NULL);
    return setv;
}

static int32_t
log_value_print(char* buf, int32_t pos, log_value_t* value, bool verbose)
{
    if (value == NULL) return pos + sprintf(buf + pos, "<null>");
    else if (verbose)
        return pos + sprintf(buf + pos, "%s<r%d,s%d>",
            value->value.a, value->ref_no, value->size);
    else return pos + sprintf(buf + pos, "%s", value->value.a);
}

static log_rule_t*
log_rule_init(log_rule_t* rule, set_t* gv)
{
    coll_alloc(&rule, sizeof(log_rule_t), ENT_RULE, gv);
    rule->is_union = false;
    log_array_init(&rule->rule, ENT_INT32, 0, gv);
    log_array_init(&rule->param, ENT_ARRAY, 0, gv);
    map_init(&rule->const_param, MAP_INT32_VALUE, 0, gv);
    map_init(&rule->param_name_map, MAP_INT32_VALUE, 0, gv);
    return rule;
}

void
log_rule_free(log_rule_t* rule)
{
    log_array_free(&rule->rule);
    log_array_free(&rule->param);
    map_free(&rule->const_param);
    map_free(&rule->param_name_map);
    coll_free_ptr(rule);
}

void
log_rule_set_init(log_rule_set_t* rs, set_t* gv)
{
    coll_alloc(&rs, sizeof(log_rule_set_t), ENT_RULE_SET, gv);
    map_init(&rs->rule_name_map, MAP_INT32_VALUE, 0, gv);
    map_init(&rs->rule_index_map,
             KEY_ID(ENT_VALUE) | VALUE_ID(ENT_INT32), 0, gv);
    map_init(&rs->rules, KEY_ID(ENT_INT32) | VALUE_ID(ENT_RULE), 0, gv);
    map_init(&rs->table_rule_map,
        KEY_ID(ENT_INT32) | VALUE_ID(ENT_ARRAY), 0, gv);
    set_init(&rs->input_tables, KEY_ID(ENT_INT32), 0, gv);
    set_init(&rs->output_tables, KEY_ID(ENT_INT32), 0, gv);
    map_init(&rs->param_size, KEY_ID(ENT_INT32) | VALUE_ID(ENT_INT32), 0, gv);
}

void
log_rule_set_free(log_rule_set_t* rs)
{
    map_free(&rs->rule_name_map);
    map_free(&rs->rule_index_map);
    map_free(&rs->rules);
    map_free(&rs->table_rule_map);
    set_free(&rs->input_tables);
    set_free(&rs->output_tables);
    map_free(&rs->param_size);
    coll_free_ptr(rs);
}

log_engine_t*
log_engine_init(log_engine_t* log, set_t* gv)
{
    coll_alloc(&log, sizeof(log_engine_t), ENT_LOG_ENG, gv);
    map_init(&log->tables, KEY_ID(ENT_INT32) | VALUE_ID(ENT_TABLE), 0, gv);
    log_rule_set_init(&log->rule_set, gv);
    log->ext_func = NULL;
    return log;
}

void
log_engine_free(log_engine_t* log)
{
    map_free(&log->tables);
    log_rule_set_free(&log->rule_set);
    coll_free_ptr(log);
}

/* --------------------------------------------------------------------------
 * TUPLES
 * --------------------------------------------------------------------------
 */

static log_config_t log_config;

void log_set_sep(char sep1, char sep2)
{
    log_config.sep1 = sep1;
    log_config.sep2 = sep2;
}

/* indexes will never be manipulated directly. use log_table_add|remove */

void
log_tuple_free(log_tuple_t* t, set_t* values, bool free_val)
{
    /* free indicates if value is freed. */

    if (free_val) {
        int i;
        for (i = 0;i < t->n_values;i++)
            if (t->values[i] != NULL)
                log_value_free(t->values[i], values);
    }

    if (t->indexes != NULL) free(t->indexes);
    free(t);
}

static void
log_tuple_set_hash_code(log_tuple_t* t, int32_t n_values)
{
    int32_t i, code;
    hash_code_array_init(&code);

    for (i = 0;i < n_values;i++) {
        /* NULL only for specifying query condition */
        if (t->values[i] != NULL)
            hash_code_array_add(&code, t->values[i]->hash_code);
    }

    hash_code_array_final(&code);
    t->hash_code = code;
}

log_tuple_t*
log_tuple_init(int32_t n_values)
{
    log_tuple_t* tuple =
        calloc(1, sizeof(log_tuple_t) + sizeof(void*) * n_values);
    tuple->n_values = n_values;
    return tuple;
}

log_tuple_t*
log_tuple_init_val(log_value_t** val, int32_t n_values)
{
    /* ref will not be updated */
    log_tuple_t* tuple = log_tuple_init(n_values);
    if (val != NULL) {
        memcpy(tuple->values, val, sizeof(void*) * n_values);
        log_tuple_set_hash_code(tuple, n_values);
    }
    return tuple;
}

static log_tuple_t*
log_tuple_clone(log_tuple_t* tuple)
{
    int i;
    log_tuple_t* nt = log_tuple_init_val(tuple->values, tuple->n_values);
    for (i = 0;i < tuple->n_values;i++) log_value_ref(tuple->values[i]);
    nt->count = tuple->count;
    return nt;
}

static log_tuple_t*
log_tuple_init_str0(const char* t, char sep, bool use_null, set_t* gv)
{
    /* the value's reference will be added */
    /* the input is in the form of n:f0: ... : fn */
    int64_t count = atoll(t);
    if (t[0] < '0' || t[0] > '9') return NULL;

    TYPE(array_t, char*) pos;
    log_array_init(&pos, 0, 0, gv);

    char* p = (char*)t;
    for (;*p != 0;p++)
        if (*p == sep) array_add(&pos, p);

    int32_t size = array_size(&pos);
    array_add(&pos, p);

    if (size == 0) {
        log_array_free(&pos);
        return NULL;
    }

    log_tuple_t* tuple = log_tuple_init(size);
    tuple->count = count;

    int i;
    for (i = 0;i < size;i++) {
        if (use_null) {
            char c = ((char*)array_get(&pos, i))[1];
            if (c == 0 || c == sep) {
                tuple->values[i] = NULL;
                continue;
            }
        }

        log_value_t* val = log_value_init((char*)array_get(&pos, i) + 1,
            (char*)array_get(&pos, i + 1) -
            ((char*)array_get(&pos, i) + 1), gv);
        tuple->values[i] = val;
    }

    log_array_free(&pos);
    log_tuple_set_hash_code(tuple, size);
    return tuple;
}

log_tuple_t*
log_tuple_init_str_null(const char* t, char sep, set_t* gv)
{
    return log_tuple_init_str0(t, sep, true, gv);
}

log_tuple_t*
log_tuple_init_str(const char* t, char sep, set_t* gv)
{
    return log_tuple_init_str0(t, sep, false, gv);
}

int32_t
log_tuple_print(char* buf, int32_t pos, log_tuple_t* t)
{
    pos += sprintf(buf + pos, "%" PRId64, t->count);
    buf[pos++] = log_config.sep1;

    int32_t i;
    for (i = 0;i < t->n_values;i++) {
        if (i > 0) buf[pos++] = log_config.sep1;
        pos = log_value_print(buf, pos, t->values[i], false);
    }
    return pos;
}

/* --------------------------------------------------------------------------
 * TABLES
 * --------------------------------------------------------------------------
 */

log_table_t*
log_table_init(log_table_t* tbl, int32_t n, int32_t f,
               int32_t size, set_t* gv)
{
    coll_alloc(&tbl, sizeof(log_table_t), ENT_TABLE, gv);

    tbl->table_index = n;
    tbl->num_fields = f;
    tbl->is_remove = false;

    map_init(&tbl->index_def,
        KEY_ID(ENT_INT_TUPLE) | VALUE_ID(ENT_INT32), 0, gv);
    log_array_init(&tbl->index_map, KEY_ID(ENT_INDEX), 0, gv);
    set_init(&tbl->tuples, KEY_ID(ENT_TUPLE), size, gv);

    tbl->tuples.aux = tbl;
    return tbl;
}

void
log_table_free(log_table_t* tbl)
{
    map_free(&tbl->index_def);
    log_array_free(&tbl->index_map);
    set_free(&tbl->tuples);
    coll_free_ptr(tbl);
}

static void
log_index_add_node0(log_tuple_t* t, int32_t i_idx)
{
    /* add first tuple for the key of index */
    log_index_i_pre(t, i_idx) = log_index_i_suc(t, i_idx) = t;
}

static void
log_index_add_node1(log_tuple_t* t, log_tuple_t* head, int32_t i_idx)
{
    log_index_i_suc(t, i_idx) = head;
    log_index_i_pre(t, i_idx) = log_index_i_pre(head, i_idx);
    log_index_i_suc(log_index_i_pre(head, i_idx), i_idx) = t;
    log_index_i_pre(head, i_idx) = t;
}

static bool
log_index_del_node(log_tuple_t* t, int32_t i_idx)
{
    /* returns true if this is the last node in link */
    if (log_index_i_pre(t, i_idx) == t) return true;

    log_index_i_suc(log_index_i_pre(t, i_idx), i_idx) =
            log_index_i_suc(t, i_idx);

    log_index_i_pre(log_index_i_suc(t, i_idx), i_idx) =
            log_index_i_pre(t, i_idx);
    return false;
}

static void
log_index_add_tuple(hash_t* index, int32_t i, log_tuple_t* t)
{
    map_node_t* node = log_hash_get(index, t);
    if (node == NULL) {
        log_index_add_node0(t, i);
        log_hash_add(index, t, NULL);
    }
    else {
        log_index_add_node1(t, (log_tuple_t*)node->key, i);
        node->key = t;
    }
}

log_tuple_t*
log_index_get_index(log_table_t* tbl, log_tuple_t* t, int32_t i_idx)
{
    /* t is key tuple */
    hash_t* index = array_get(&tbl->index_map, i_idx);
    map_node_t* node = log_hash_get(index, t);

    if (node == NULL) return NULL;
    return (log_tuple_t*)log_hash_get(index, t)->key;
}

static void
log_table_add0(log_table_t* tbl, log_tuple_t* t)
{
    /* assume tuple is not present in table, need not free t afterwards */
    /* check where tuple count is set to 1 */
    log_hash_add(&tbl->tuples, t, NULL);
    int n_idx = array_size(&tbl->index_def);
    if (n_idx > 0) t->indexes = calloc(n_idx * 2, sizeof(void*));

    /* update index */
    int i;
    for (i = 0;i < n_idx;i++) {
        hash_t* index = array_get(&tbl->index_map, i);
        log_index_add_tuple(index, i, t);
    }
}

static void
log_table_remove0(log_table_t* tbl, log_tuple_t* t)
{
    /* assume tuple is present in table, t has been freed afterwards */
    int i;
    /* update index */
    int n_idx = array_size(&tbl->index_def);

    for (i = 0;i < n_idx;i++) {
        bool last = log_index_del_node(t, i);
        hash_t* index = array_get(&tbl->index_map, i);
        map_node_t* node = log_hash_get(index, t);

        if (last) log_hash_del(index, t);
        else if (node->key == t) node->key = log_index_i_suc(t, i);
    }

    log_hash_del(&tbl->tuples, t);
}

static void
log_table_add_extra(log_table_t* tbl, log_tuple_t* t)
{
    /* add or merge count, will be referred (add) or freed (merge count) */
    log_tuple_t* et = set_get(&tbl->tuples, t);
    if (et == NULL) log_table_add0(tbl, t);
    else {
        et->count += t->count;
        log_tuple_free(t, tbl->m.glb_values, true);
    }
}

void
log_table_add(log_table_t* tbl, log_tuple_t* t)
{
    /* validation, t not in table */
    ovs_assert(!set_has(&tbl->tuples, t) && tbl->num_fields == t->n_values);
    log_table_add0(tbl, t);
}

void
log_table_remove(log_table_t* tbl, log_tuple_t* t)
{
    /* validation, must have this and t is from table */
    ovs_assert(set_get(&tbl->tuples, t) == t);
    log_table_remove0(tbl, t);
}

int32_t
log_table_add_index(log_table_t* tbl, log_int_tuple_t* index_key)
{
    /* add new index for table or returning existing one */
    /* index_key will be cloned */

    map_node_t* index = log_hash_get(&tbl->index_def, index_key);
    if (index != NULL) return ptr2i(index->value);

    log_int_tuple_t* ikey = log_int_tuple_clone(index_key);
    int32_t index_id = map_size(&tbl->index_def);
    map_add(&tbl->index_def, ikey, i2ptr(index_id));

    map_t* new_i = log_hash_init(NULL, COLL_ID(ENT_INDEX),
        SZ_INIT_HASH, tbl->m.glb_values);
    array_add(&tbl->index_map, new_i);
    new_i->aux = ikey;

    SET_ALL(&tbl->tuples, tuple, log_tuple_t*)
        tuple->indexes = realloc(
            tuple->indexes, (index_id + 1) * 2 * sizeof(void*));
        log_index_add_tuple(new_i, index_id, tuple);
    SET_END

    return index_id;
}

int32_t
log_index_print(char* buf, int32_t pos, log_table_t* t)
{
    int i = 0, j = 0;
    ARRAY_ALL(&t->index_map, index, hash_t*)
        log_int_tuple_t* def = index->aux;
        pos += sprintf(buf + pos, "  index=");
        pos = log_int_tuple_print(buf, pos, def);
        buf[pos++] = '\n';

        SET_ALL(index, key, log_tuple_t*)
            pos += sprintf(buf + pos, "  key set: ");
            INDEX_ALL(key, i, t1)
                pos = log_tuple_print(buf, pos, t1);
                buf[pos++] = ' ';

                if (++j > 200) {
                    pos += sprintf(buf + pos, "  ...\n");
                    return pos;
                }
            INDEX_END
            buf[pos++] = '\n';
        SET_END
        i++;
    ARRAY_END
    return pos;
}

int32_t
log_table_print(char* buf, int32_t pos, log_table_t* t, bool verbose)
{
    if (verbose) {
        pos += sprintf(buf + pos, "  tbl id=%d fd=%d sz=%d\n",
            t->table_index, t->num_fields, table_size(t));
    }
    pos = log_hash_print(buf, pos, &t->tuples, verbose);
    if (verbose) pos = log_index_print(buf, pos, t);
    return pos;
}

int32_t
log_rule_set_print(char* buf, int32_t pos, log_rule_set_t* rs)
{
    pos += sprintf(buf + pos, "rule_name_map\n");
    pos = log_hash_print(buf, pos, &rs->rule_name_map, false);

    pos += sprintf(buf + pos, "\nrule_index_map\n");
    pos = log_hash_print(buf, pos, &rs->rule_index_map, false);

    pos += sprintf(buf + pos, "\ntable_rule_map\n");
    pos = log_hash_print(buf, pos, &rs->table_rule_map, false);

    pos += sprintf(buf + pos, "\nparam_size\n");
    pos = log_hash_print(buf, pos, &rs->param_size, false);

    pos += sprintf(buf + pos, "\ninput_tables\n");
    pos = log_hash_print(buf, pos, &rs->input_tables, false);

    pos += sprintf(buf + pos, "\noutput_tables\n");
    pos = log_hash_print(buf, pos, &rs->output_tables, false);

    pos += sprintf(buf + pos, "\nrules\n");
    pos = log_hash_print(buf, pos, &rs->rules, false);
    return pos;
}

static int32_t
log_rule_print(char* buf, int32_t pos, log_rule_t* r)
{
    pos += sprintf(buf + pos, r->is_union ? "(union," : "(join,");
    pos += sprintf(buf + pos, "rule=");
    pos = log_array_print(buf, pos, &r->rule, false);
    pos += sprintf(buf + pos, ",param=");
    pos = log_array_print(buf, pos, &r->param, false);
    pos += sprintf(buf + pos, ",name=");
    pos = log_hash_print(buf, pos, &r->param_name_map, false);
    pos += sprintf(buf + pos, ",const=");
    pos = log_hash_print(buf, pos, &r->const_param, false);
    pos += sprintf(buf + pos, ")\n");
    return pos;
}

int32_t
log_coll_print(char* buf, int pos, void* item, int32_t type, bool verbose)
{
    /* do not check the buf limit */
    if (item == NULL && type != ENT_INT32 && type != ENT_TST_INT32)
        return pos;

    else if (type == ENT_INT32 || type == ENT_TST_INT32)
        pos += sprintf(buf + pos, "%d", ptr2i(item));
    else if (type == ENT_STR)
        pos += sprintf(buf + pos, "%s", (const char*)item);
    else if (type == ENT_VALUE)
        pos = log_value_print(buf, pos, item, verbose);
    else if (type == ENT_INT_TUPLE)
        pos = log_int_tuple_print(buf, pos, item);
    else if (type == ENT_TUPLE)
        pos = log_tuple_print(buf, pos, item);
    else if (type == ENT_ARRAY)
        pos = log_array_print(buf, pos, item, verbose);
    else if (type == ENT_SET || type == ENT_MAP)
        pos = log_hash_print(buf, pos, item, verbose);
    else if (type == ENT_TABLE)
        pos = log_table_print(buf, pos, item, verbose);
    else if (type == ENT_RULE)
        pos = log_rule_print(buf, pos, item);
    else if (type == ENT_RULE_SET)
        pos = log_rule_set_print(buf, pos, item);
    return pos;
}

/* ==========================================================================
 * SYNTAX PROCESSING
 * ==========================================================================
 */

/*
 * token of id: [a-zA-Z_][a-zA-Z0-9_]*
 * all upper case: output table; all lower case: input table; others:
 * intermediate.
 * <table_name> ( <param_name>, ... ) ':'|'>' <table_name> (
 *   <param_name> | 'value' | - ), ... ;
 * ':' is for join. '>' is for union. order is always important
 * special table: not used now, e.g., could be used to specify language
 * parameters. join is preferred with external function as there is more
 * flexibility in param. comments start with # document started with ##
 */

struct log_sync_s {
    const char* text;
    int len;

    int curpos;
    char curchar;
    char curtoken;

    char token[LOG_TOKEN_SZ];
    int token_pos;
    set_t* gv;
};

static struct log_sync_s sync;

void
log_sync_init(const char* log, set_t* gv)
{
    sync.len = strlen(log);
    sync.text = log;
    sync.curpos = 0;
    sync.token_pos = 0;
    sync.gv = gv;
}

static void
sync_getc(void)
{
    sync.curchar = sync.text[sync.curpos++];
}

static bool
sync_eof(void)
{
    return sync.curpos >= sync.len;
}

static void
sync_error(const char* s0, const log_value_t* s1)
{
    printf("syntax error: %s %s \n%s\n", s0,
        s1 == NULL ? "" : s1->value.a,
        sync.text + sync.curpos);
    exit(1);
}

static void
sync_init_token(void)
{
    sync.token_pos = 0;
}

static log_value_t*
sync_get_value(void)
{
    log_value_t* token = log_value_init(sync.token, sync.token_pos, sync.gv);
    return token;
}

static log_value_t*
sync_get_const(const char* c)
{
    log_value_t* token = log_value_init(c, 0, sync.gv);
    return token;
}

static void
sync_append_c(void)
{
    sync.token[sync.token_pos++] = sync.curchar;
    sync_getc();
    if (sync.token_pos >= LOG_TOKEN_SZ) sync_error("token too long", 0);
}

static void
sync_gett(void)
{
    bool in_comment = false;
    bool in_literal = false;
    bool in_ident = false;

    while (!sync_eof()) {
        if (in_comment) {
            if (sync.curchar == '\n') {
                in_comment = false;
            }
            sync_append_c();
        }
        else if (in_literal) {
            if (sync.curchar == '\'') {
                sync_getc();
                sync.curtoken = 's';
                return;
            }
            else {
                sync_append_c();
            }
        }
        else if (in_ident) {
            if (sync.curchar != '_' && !isalpha(sync.curchar)
                && !isdigit(sync.curchar)) {
                sync.curtoken = 't';
                return;
            }
            sync_append_c();
        }
        else {
            if (sync.curchar == '#') {
                in_comment = true;
                sync_getc();
            }
            else if (sync.curchar == '\'') {
                in_literal = true;
                sync_init_token();
                sync_getc();
            }
            else if (sync.curchar == '_' || isalpha(sync.curchar)) {
                sync_init_token();
                sync_append_c();
                in_ident = true;
            }
            else if (strchr(":>().,-;", sync.curchar) != NULL) {
                sync.curtoken = sync.curchar;
                sync_getc();
                return;
            }
            else if (isspace(sync.curchar)) sync_getc();
            else if (sync.curchar == '\n') sync_getc();
            else sync_error("unknown char near", 0);
        }
    }

    /* for last period without following chars */
    sync.curtoken = sync.curchar;
}

static void
sync_nt_params(array_t* list)
{
    /* ( ( param | 'literal' | - )* , ) */
    if (sync.curtoken != '(') sync_error("expecting (", 0);
    sync_gett();

    for (;;) {
        if (sync.curtoken == 't') {
            array_add(list, sync_get_const("t"));
            array_add(list, sync_get_value());
        }
        else if (sync.curtoken == '-') {
            array_add(list, sync_get_const("-"));
            array_add(list, NULL);
        }
        else if (sync.curtoken == 's') {
            array_add(list, sync_get_const("s"));
            array_add(list, sync_get_value());
        }
        else sync_error("expecting param, literal, or -", NULL);

        sync_gett();
        if (sync.curtoken == ',') {
            sync_gett();
            continue;
        }
        else if (sync.curtoken == ')') {
            sync_gett();
            return;
        }
        else sync_error("expecting , or )", NULL);
    }
}

static void
sync_nt_table(array_t* list)
{
    if (sync.curtoken != 't') sync_error("table name expected", NULL);
    log_value_t* table_name = sync_get_value();

    sync_gett();
    array_add(list, NULL); /* will be overrided later */
    array_add(list, table_name);
    sync_nt_params(list);
}

void
log_sync_parse(map_t* sem)
{
    /*
     * tableName -> (left side, right side table 0, right side table 1, ...)
     * each table contains (table name, param0, param1, ...)
     */

    map_init(sem, KEY_ID(ENT_VALUE) | VALUE_ID(ENT_ARRAY), 0, sync.gv);
    sync.gv = sem->m.glb_values;

    sync_getc();
    sync_gett();

    for (;;) {
        array_t* tables = log_array_init(NULL, KEY_ID(ENT_ARRAY), 0, sync.gv);
        array_t* tbl = log_array_init(NULL, KEY_ID(ENT_VALUE), 0, sync.gv);

        sync_nt_table(tbl);
        array_add(tables, tbl);
        log_value_t* table_name = array_get(tbl, 1);

        if (sync.curtoken != ':' && sync.curtoken != '>') {
            sync_error("expecting : or >", NULL);
        }

        array_set(tbl, 0, sync_get_const(sync.curtoken == '>' ? "u" : "j"));
        sync_gett();

        for (;;) {
            tbl = log_array_init(NULL, KEY_ID(ENT_VALUE), 0, sync.gv);
            sync_nt_table(tbl);
            array_add(tables, tbl);
            if (sync.curtoken == ';' || sync.curtoken == '.') break;
        }

        if (map_get(sem, table_name) != NULL) {
            sync_error("definition existed: ", table_name);
        }

        map_add(sem, table_name, tables);
        if (sync.curtoken == ';') sync_gett();
        else if (sync.curtoken == '.') return;
    }
}

/* ==========================================================================
 * SYNTAX PROCESSING
 * ==========================================================================
 */

void
log_sort_array(int start, array_t* list, array_t* sem1, array_t* sem2)
{
    /* this must be stable sort. see the sort for table size */

    int i, j;
    for (i = start;i < list->size;i++) {
        int index = i;

        for (j = i + 1;j < list->size;j++)
            if (ptr2i(list->item[j]) < ptr2i(list->item[index]))
                index = j;

        void* newi = (void*)list->item[index];
        void* newv1 = sem1 == NULL ? NULL : (void*)sem1->item[index];
        void* newv2 = sem2 == NULL ? NULL : (void*)sem2->item[index];

        memmove(&list->item[i + 1], &list->item[i],
                (index - i) * sizeof(void*));

        if (sem1 != NULL)
            memmove(&sem1->item[i + 1], &sem1->item[i],
                    (index - i) * sizeof(void*));
        if (sem2 != NULL)
            memmove(&sem2->item[i + 1], &sem2->item[i],
                    (index - i) * sizeof(void*));

        list->item[i] = newi;
        if (sem1 != NULL) sem1->item[i] = newv1;
        if (sem2 != NULL) sem2->item[i] = newv2;
    }
}

int
log_insert_item(int val, array_t* list, void* obj1,
                void* obj2, array_t* sem1, array_t* sem2)
{
    /*
     * returns -1 if there is no equal value in the list, or the position to
     * insert. If there is tie, the position is after all items of equal
     * value. will insert only if there is no equal value.
     */

    int count;
    for (count = 0;count < list->size;count++) {
        if (val < ptr2i(list->item[count])) break;
    }

    array_ins(list, count, i2ptr(val));
    if (sem1 != NULL) array_ins(sem1, count, obj1);
    if (sem2 != NULL) array_ins(sem2, count, obj2);
    return count;
}

void
log_topo_sort(TYPE2(map_t*, log_value_t*, set_t*) g, /* set of value */
              TYPE(array_t* order, log_value_t*),
              TYPE(set_t*, log_value_t*) in_nodes,
              TYPE(set_t*, log_value_t*) out_nodes)
{
    /* input g will be destroyed after sort */

    set_t* gv = g->m.glb_values;
    log_array_init(order, KEY_ID(ENT_VALUE), 0, gv);
    set_init(in_nodes, KEY_ID(ENT_VALUE), 0, gv);
    set_init(out_nodes, KEY_ID(ENT_VALUE), 0, gv);

    set_t right_nodes, all_nodes, to_remove;
    set_init(&right_nodes, KEY_ID(ENT_VALUE), 0, gv);
    set_init(&all_nodes, KEY_ID(ENT_VALUE), 0, gv);

    MAP_ALL(g, node)
        set_add(&all_nodes, node->key);

        SET_ALL(node->value, node1, log_value_t*)
            set_add(&all_nodes, node1);
            set_add(&right_nodes, node1);
        SET_END /* end of iteration */
    MAP_END /* end of iteration */

    SET_ALL(&all_nodes, key, log_value_t*)
        if (!map_has(g, key)) set_add(in_nodes, key);
        else if (!set_has(&right_nodes, key))
            set_add(out_nodes, key);
    SET_END /* end of iteration */

    while (set_size(&all_nodes) > 0) {
        log_value_t* next = NULL;

        SET_ALL(&all_nodes, key, log_value_t*)
            if (!map_has(g, key)) {
                next = key;
                SET_EXIT;
            }
        SET_END

        if (next == NULL)
            sync_error("circular graph, check around ",
                       log_hash_get_one(&all_nodes));

        array_add(order, next);
        set_del(&all_nodes, next);
        set_init(&to_remove, KEY_ID(ENT_VALUE), 0, gv);

        MAP_ALL(g, node)
            set_del(node->value, next);
            if (set_size((set_t*)node->value) == 0)
                set_add(&to_remove, node->key);
        MAP_END

        SET_ALL(&to_remove, key, log_value_t*)
            set_free(map_del(g, key));
        SET_END
        set_free(&to_remove);
    }

    set_free(&right_nodes);
    set_free(&all_nodes);
    map_free(g);
}

static int
check_name(log_value_t* t)
{
    /* check if string are in all lower case (> 0), all upper case (<0)
     * or mixed (== 0)
     */
    const char* s = t->value.a;
    bool lower = false;
    bool upper = false;
    char c;

    while ((c = *s++) != 0) {
        if (islower(c)) lower = true;
        else if (isupper(c)) upper = true;
    }

    if (lower && upper) return 0;
    else if (lower) return 1;
    else if (upper) return -1;
    else return 0;
}

/* ==========================================================================
 * SEMANTICS DEFINITION
 * ==========================================================================
 */

void
log_sem_process(log_rule_set_t* rule_set, map_t* sem)
{
    /* string -> array of array of string */
    set_t* gv = sem->m.glb_values;
    /* STEP 1: check table dependency and assign digit table / rule index */
    map_t rules; /* map string to (set of value) */
    map_init(&rules, KEY_ID(ENT_VALUE) | VALUE_ID(ENT_SET), 0, gv);

    log_value_t* rname;
    MAP_ALL(sem, node)
        rname = NULL;
        set_t* dep = set_init(NULL, KEY_ID(ENT_VALUE), 0, gv);

        ARRAY_ALL((array_t*)node->value, t, array_t*)
            log_value_t* nm = array_get(t, 1);
            if (rname == NULL) rname = nm;
            else set_add(dep, nm);
        ARRAY_END
        map_add(&rules, rname, dep);
    MAP_END

    array_t topo_order;
    set_t topo_in, topo_out;
    log_topo_sort(&rules, &topo_order, &topo_in, &topo_out);

    int32_t rule_index = 0;
    ARRAY_ALL(&topo_order, name, log_value_t*)
        map_add(&rule_set->rule_name_map, i2ptr(rule_index), name);
        map_add(&rule_set->rule_index_map, name, i2ptr(rule_index++));
    ARRAY_END

    /* STEP 2: check upper case, lower case and mixed */
    SET_ALL(&topo_in, name, log_value_t*)
        if (check_name(name) <= 0)
            sync_error("input must be all lower case: ", name);

        set_add(&rule_set->input_tables,
                map_get(&rule_set->rule_index_map, name));
    SET_END

    SET_ALL(&topo_out, name, log_value_t*)
        if (check_name(name) >= 0)
            sync_error("output must be all upper case: ", name);

        set_add(&rule_set->output_tables,
                map_get(&rule_set->rule_index_map, name));
    SET_END

    set_t intr;
    set_init(&intr, KEY_ID(ENT_VALUE), 0, gv);

    MAP_ALL(sem, name)
        if (map_has(&topo_out, i2ptr(name->key))) continue;
        if (check_name(i2ptr(name->key)) != 0)
            sync_error("intermediate must be mixed: ", name->key);
    MAP_END

    /*
     * STEP 3: check table size consistency and assign digit index.
     * and if union / join on itself, it could only perform twice on
     * each param, i.e., X : A, A, A is not supported.
     */
    map_t table_size;
    map_init(&table_size, KEY_ID(ENT_VALUE), 0, gv); /* map string to int */

    MAP_ALL(sem, name)
        array_t* val = name->value; /* array of array of value */
        log_rule_t* rule = log_rule_init(NULL, gv);

        /* rule_id is integer */
        void* rule_id = map_get(&rule_set->rule_index_map, name->key);
        map_add(&rule_set->rules, rule_id, rule);

        log_value_t* rule_t = array_get(array_get(val, 0), 0);
        rule->is_union = strcmp("u", rule_t->value.a) == 0;

        int const_value = -2; /* -1 is for ignore */

        /* reorder table sequence */
        ARRAY_ALL(val, t, array_t*)
            log_value_t* table_name = array_get(t, 1);
            void* rule_id = map_get(&rule_set->rule_index_map, table_name);
            array_add(&rule->rule, rule_id);
        ARRAY_END

        int i;
        log_sort_array(1, &rule->rule, val, NULL);

        for (i = 2;i < rule->rule.size - 1;i++) {
            if (array_get(&rule->rule, i - 1) == array_get(&rule->rule, i) &&
                array_get(&rule->rule, i + 1) == array_get(&rule->rule, i))
                sync_error(
                        "cannot join / union on itself for more than twice: ",
                        name->key);
        }

        int param_size = 0;
        bool is_left = true;
        bool left_has_param = false;
        bool left_has_value = false;

        map_t param_map; /* map string to integer */
        map_init(&param_map, KEY_ID(ENT_VALUE) | VALUE_ID(ENT_INT32), 0, gv);

        ARRAY_ALL(val, t, array_t*)
            array_t* param_list = log_array_init(NULL, KEY_ID(ENT_INT32),
                                                 0, gv);
            array_add(&rule->param, param_list);
            log_value_t* table_name = array_get(t, 1);

            int32_t size = ((array_t*)t)->size / 2 - 1;
            int32_t table_id = map_get_int(
                                &rule_set->rule_index_map, table_name);
            map_add(&rule_set->param_size, i2ptr(table_id), i2ptr(size));

            /* check table size */
            if (rule->is_union) {
                if (is_left) param_size = size;
                else if (size != param_size)
                    sync_error("table param size mismatch in union rule: ",
                               name->key);
            }
            else {
                struct map_node_s* ksize = log_hash_get(
                                           &table_size, table_name);
                if (ksize == NULL)
                    map_add(&table_size, table_name, i2ptr(size));

                else if (ptr2i(ksize->value) != size)
                    sync_error("table param size mismatch in join rule: " ,
                               name->key);
            } /* if check table size */

            /* assign index to each param */
            for (i = 0; i < size;i++) {
                log_value_t* param_type = array_get(t, i * 2 + 2);
                log_value_t* param_value = array_get(t, i * 2 + 3);

                if (is_left && strcmp(param_type->value.a, "-") == 0)
                    sync_error("left cannot have 'ignore': ", name->key);

                if (strcmp(param_type->value.a, "-") == 0) {
                    array_add(param_list, i2ptr(-1));
                }

                else if (strcmp(param_type->value.a, "t") == 0) {
                    if (is_left) left_has_param = true;
                    map_node_t* param_no = log_hash_get(
                                           &param_map, param_value);

                    void* no; /* type is int */
                    if (param_no == NULL) {
                        no = i2ptr(param_map.size);
                        map_add(&param_map, param_value, no);
                        map_add(&rule->param_name_map, no, param_value);
                    } else no = param_no->value;
                    array_add(param_list, no);
                }

                else if (strcmp(param_type->value.a, "s") == 0) {
                    if (is_left) left_has_value = true;
                    void* c_value = param_value;
                    map_add(&rule->const_param, i2ptr(const_value), c_value);
                    array_add(param_list, i2ptr(const_value--));
                }
            } /* for each table param */
            is_left = false;
        ARRAY_END /* for each table */

        map_free(&param_map);
        if (!left_has_param)
        sync_error("left must have param: ", name->key);
        if (rule->is_union && left_has_value)
        sync_error("left cannot have const: ", name->key);
    MAP_END /* for each rule */

    /* STEP 4: check param reference. */
    MAP_ALL(&rule_set->rules, rule_no)
        array_t* left_param = NULL; /* array of int, for checking union */

        log_rule_t* rule = map_get(&rule_set->rules, rule_no->key);
        log_value_t* rule_name = map_get(
                &rule_set->rule_name_map, rule_no->key);

        /* add table rule map */
        int32_t i;
        for (i = 1;i < rule->rule.size;i++) {
            array_t* set = map_get(&rule_set->table_rule_map,
                array_get(&rule->rule, i));

            if (set == NULL) {
                set = log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);
                map_add(&rule_set->table_rule_map,
                        array_get(&rule->rule, i), set);
            }

            int32_t found = log_array_look_for(set, rule_no->key);
            if (found < 0) array_add(set, rule_no->key);
        }

        ARRAY_ALL(&rule->param, param, array_t*)
            /* param is array of int */
            if (left_param == NULL) left_param = param;

            if (rule->is_union) {
                if (left_param != NULL) {
                    bool not_found = false;

                    ARRAY_ALL(left_param, item, void*)
                        if (log_array_look_for(param, item) < 0) {
                            not_found = true;
                            ARRAY_EXIT;
                        }
                    ARRAY_END

                    if (not_found)
                        sync_error("union param not found in ", rule_name);
                }
                continue;
            }

            /*
             * for right side param, it must also appear either in left
             * side or right side or being 'ignored'; for left side param,
             * it must appear in right side
             */
            ARRAY_ALL((array_t*)param, p0no, void*)
                int32_t p0 = ptr2i(p0no);
                if (p0 < 0) continue;

                bool found = false;
                ARRAY_ALL(&rule->param, param1, array_t*)
                    if (param == param1) continue;

                    if (log_array_look_for(param1, p0no) >= 0) {
                        found = true;
                        ARRAY_EXIT;
                    }
                ARRAY_END

                if (!found)
                sync_error("not used / undefined param ", rule_name);
            ARRAY_END
        ARRAY_END /* for each table */
    MAP_END /* for each rule */

    /* STEP 5: sort table_rule_map */
    MAP_ALL(&rule_set->table_rule_map, node)
        array_t* list = node->value;
        log_sort_array(0, list, NULL, NULL);
    MAP_END

    set_free(&intr);
    set_free(&topo_in);
    set_free(&topo_out);
    map_free(&table_size);
    log_array_free(&topo_order);
}

/* ==========================================================================
 * TABLE OPERATION
 * ==========================================================================
 */

static log_tuple_t*
tblopr_reorder_tuple(log_tuple_t* t, TYPE(array_t*, int32_t) order,
                     TYPE2(map_t*, int32_t, log_value_t*) const_map)
{
    /* input and output table could be different. order is sequence
     * instead of param index.
     * (a, b, c, d, e) + (2, -2, 1, 4) => (c, C[-2], b, e)
     */
    log_tuple_t* newt = log_tuple_init(array_size(order));
    int i;
    for (i = 0;i < array_size(order);i++) {
        log_value_t* value;
        int32_t order_i = array_get_int(order, i);

        if (order_i >= 0) value = t->values[order_i];
        else if (order_i < -1) value = map_get(const_map, i2ptr(order_i));
        else ovs_assert(false); /* reorder sees constants */

        log_value_ref(value);
        newt->values[i] = value;
    }

    newt->count = t->count;
    log_tuple_set_hash_code(newt, array_size(order));
    return newt;
}

static void
tblopr_reorder_table(log_table_t* input, TYPE(array_t*, int32_t) order,
                     TYPE2(map_t*, int32_t, log_value_t*) const_map,
                     log_table_t* output)
{
    /* input and output table could be different */
    SET_ALL(&input->tuples, t, log_tuple_t*)
        log_table_add(output, tblopr_reorder_tuple(t, order, const_map));
    SET_END
}

static bool
tblopr_match_const(log_tuple_t* t, TYPE(array_t*, int32_t) cpos,
                   log_value_t** cval)
{
    int i;
    for (i = 0;i < array_size(cpos);i++) {
        int32_t ci = array_get_int(cpos, i);
        if (t->values[ci] != cval[i]) return false;
    }
    return true;
}

static log_table_t*
tblopr_query_table(log_table_t* input, TYPE(array_t*, int32_t) param,
                   log_value_t** val)
{
    /* input only used for get table param */

    log_table_t* output =
        log_table_init(NULL, input->table_index, input->num_fields,
            0, input->m.glb_values);

    if (array_size(param) == 0) {
        SET_ALL(&input->tuples, t, log_tuple_t*)
            log_tuple_t* nt = log_tuple_clone(t);
            log_table_add(output, nt);
        SET_END
        return output;
    }

    log_int_tuple_t* index = log_int_tuple_init(param);
    int32_t idx = log_table_add_index(input, index);
    log_int_tuple_free(index);

    log_tuple_t* key = log_tuple_init_val(val, array_size(param));
    log_tuple_t* set = log_index_get_index(input, key, idx);

    /* check set is null? */
    INDEX_ALL(set, idx, t)
        log_tuple_t* nt = log_tuple_clone(t);
        log_table_add(output, nt);
    INDEX_END

    log_tuple_free(key, input->m.glb_values, false);
    return output;
}

static void
tblopr_merge_tuple(log_table_t* tbl, log_tuple_t* tup,
                   bool negative, bool free_t)
{
    /* tuple untouched */
    log_tuple_t* org_tuple = set_get(&tbl->tuples, tup);

    if (org_tuple == NULL) {
        log_tuple_t* nt = free_t ? tup : log_tuple_clone(tup);
        log_table_add0(tbl, nt);
    }
    else {
        if (negative) org_tuple->count -= tup->count;
        else org_tuple->count += tup->count;
        if (free_t) log_tuple_free(tup, tbl->m.glb_values, true);
    }
}

static void
tblopr_merge_table(log_table_t* src, log_table_t* dst, bool negative)
{
    SET_ALL(&src->tuples, t, log_tuple_t*)
        tblopr_merge_tuple(dst, t, negative, false);
    SET_END
}

static void
tblopr_final_delta(log_table_t* source, log_table_t* dest)
{
    if (source->is_remove) {
        SET_ALL(&source->tuples, t, log_tuple_t*)
            log_tuple_t* ot = set_get(&dest->tuples, t);
            log_table_remove0(dest, ot);
        SET_END
    }
    else {
        SET_ALL(&source->tuples, t, log_tuple_t*)
            ovs_assert(set_get(&dest->tuples, t) == NULL);
            log_tuple_t* nt = log_tuple_clone(t);
            log_table_add0(dest, nt);
        SET_END
    }
}

static void
tblopr_match_reorder_and_merge(log_table_t* input, log_table_t* output,
                               TYPE(array_t*, int32_t) parami,
                               TYPE(array_t*, int32_t) paramo,
                               TYPE2(map_t*, int32_t, log_value_t*) const_map)
{
    /* example: output(0, 1, 2)  input(2, 1, -, 'const', 0)
     * input count is ignored. parami/o is param number, not
     * sequence number.
     */

    set_t* gv = input->m.glb_values;
    TYPE(array_t*, int32_t) cpos = log_array_init(
                                   NULL, KEY_ID(ENT_INT32), 0, gv);
    TYPE(array_t*, int32_t) order = log_array_init(
                                    NULL, KEY_ID(ENT_INT32), 0, gv);
    int pos = 0, i;

    for (i = 0;i < array_size(parami);i++) {
        int32_t c = array_get_int(parami, i);
        if (c < -1) array_add(cpos, i2ptr(i));
        else if (c == -1) continue;
        else {
            int32_t op = log_array_look_for(parami, array_get(paramo, pos++));
            if (op >= 0) array_add(order, i2ptr(op));
        }
    }

    log_value_t** cval = calloc(array_size(cpos), sizeof(void*));
    for (i = 0;i < array_size(cpos);i++)
        cval[i] = (log_value_t*)
                  map_get(const_map, array_get(parami,
                  array_get_int(cpos, i)));

    SET_ALL(&input->tuples, t, log_tuple_t*)
        if (tblopr_match_const(t, cpos, cval)) {
            log_tuple_t* nt = tblopr_reorder_tuple(t, order, NULL);
            log_table_add_extra(output, nt);
        }
    SET_END

    free(cval);
    log_array_free(cpos);
    log_array_free(order);
}

static void
tblopr_combine_tuple(log_table_t* res, int32_t tuple1_count,
                     log_join_param_t* joinp, int r1_fnum,
                     log_tuple_t* tuple2, log_value_t** tuple_values)
{
    int i;
    for (i = 0;i < array_size(&joinp->rem2);i++)
        tuple_values[i + r1_fnum] = tuple2->values[
            ptr2i(array_get(&joinp->rem2, i))];

    int32_t res_num_fields = res->num_fields;
    log_tuple_t* nt = log_tuple_init_val(tuple_values, res->num_fields);
    nt->count = tuple1_count;

    for (i = 0;i < res_num_fields;i++) log_value_ref(nt->values[i]);
    tblopr_merge_tuple(res, nt, false, true);
}

static log_table_t*
tblopr_cond_join(log_table_t* t1, log_table_t* t2, log_join_param_t* joinp)
{
    /*
     * t1 is intermediate table during join; t2 is original table.
     * select values joinp.select1 from t1 and const, and match that with
     * params indicated by joinp.index2.
     */
    set_t* gv = t1->m.glb_values;

    int32_t r1_fnum = array_size(&joinp->rem1);
    int32_t r2_fnum = array_size(&joinp->rem2);

    log_table_t* res = log_table_init(NULL, -1, r1_fnum + r2_fnum, 0, gv);
    int32_t t2_index = map_get_int(&t2->index_def, joinp->index2);

    int t1val_sz = array_size(&joinp->select1);
    TYPE(array_t*, int32_t) t1param = log_array_init(
        NULL, KEY_ID(ENT_INT32), t1val_sz, gv);
    log_tuple_t* key_tuple = log_tuple_init_val(NULL, t1val_sz);

    int i;
    for (i = 0;i < t1val_sz;i++) {
        log_value_t* obj = array_get(&joinp->select1, i);
        if (obj != NULL) {
            array_add(t1param, i2ptr(-1)); /* mark as not set */
            key_tuple->values[i] = obj;
        }
        else array_add(t1param, array_get(&joinp->select1i, i));
    }

    /* loop over t1 and join */
    log_value_t** tuple_values = calloc(sizeof(void*), res->num_fields);
    SET_ALL(&t1->tuples, tuple1, log_tuple_t*)

        for (i = 0;i < array_size(t1param);i++) {
            int32_t t1p = ptr2i(array_get(t1param, i));
            if (t1p < 0) continue;
            key_tuple->values[i] = tuple1->values[t1p];
        }

        log_tuple_set_hash_code(key_tuple, t1val_sz);
        log_tuple_t* match_tuples =
                log_index_get_index(t2, key_tuple, t2_index);

        if (match_tuples != NULL) { /* do not use continue */
            for (i = 0;i < r1_fnum;i++)
                tuple_values[i] =
                    tuple1->values[ptr2i(array_get(&joinp->rem1, i))];

            /* join the value */
            INDEX_ALL(match_tuples, t2_index, tuple2)
                tblopr_combine_tuple(res, tuple1->count,
                    joinp, r1_fnum, tuple2, tuple_values);
            INDEX_END
        }
    SET_END

    log_tuple_free(key_tuple, t1->m.glb_values, false);
    log_array_free(t1param);
    free(tuple_values);
    return res;
}

static void
tblopr_gen_delta(log_table_t* source, log_table_t* dest)
{
    bool is_remove = source->is_remove;
    set_t* gv = dest->m.glb_values;

    SET_ALL(&source->tuples, st, log_tuple_t*)
        ovs_assert(st->indexes == NULL);

        int64_t st_count = st->count;
        log_tuple_t* dt = set_get(&dest->tuples, st);

        if (is_remove) {
            ovs_assert(dt != NULL && dt->count >= st_count);
            if (dt->count > st_count) {
                dt->count -= st_count;
                SET_REMOVE_ITEM;
                log_tuple_free(st, gv, true);
            }
        }
        else {
            if (dt != NULL) {
                dt->count += st_count;
                SET_REMOVE_ITEM;
                log_tuple_free(st, gv, true);
            }
        }
    SET_END
}

static void
tblopr_merge_delta(log_table_t* source, log_table_t* dest,
                   log_table_t* dest_ivt)
{

    /* dest is of the same operation as source, while destIvt is opposite. */
    ovs_assert(source->table_index == dest->table_index);
    set_t* gv = dest->m.glb_values;

    SET_ALL(&source->tuples, st, log_tuple_t*)
        ovs_assert(st->indexes == NULL);
        log_tuple_t* dt = set_get(&dest->tuples, st);

        if (dt != NULL) {
            SET_REMOVE_ITEM;
            dt->count += st->count; /* count will not change hash */
            log_tuple_free(st, gv, true);
            /* will not match opposite */
        }
        else {
            log_tuple_t* dt_ivt = set_get(&dest_ivt->tuples, st);
            /* will be added later for dt_ivt == NULL */
            if (dt_ivt != NULL) {
                /* cross merge */
                long st_count = st->count;
                dt_ivt->count -= st_count;

                if (dt_ivt->count >= 0) {
                    SET_REMOVE_ITEM;
                    log_tuple_free(st, gv, true);
                }

                if (dt_ivt->count == 0) log_table_remove0(dest_ivt, dt_ivt);
                else if (dt_ivt->count < 0) { /* move to opposite table */
                    dt_ivt->count = -dt_ivt->count;
                    log_tuple_t* nt = log_tuple_clone(dt_ivt);
                    log_table_add(dest, nt);
                    log_table_remove0(dest_ivt, dt_ivt);
                }
            }
        }
    SET_END /* for source tuple */

    /* add remaining */
    SET_ALL(&source->tuples, t, log_tuple_t*)
        log_tuple_t* nt = log_tuple_clone(t);
        log_table_add0(dest, nt);
    SET_END
}

static log_table_t*
tblopr_full_join(log_table_t* t1, log_table_t* t2, log_join_param_t* joinp)
{
    /* select1 contains only constants */

    int32_t r1_fnum = array_size(&joinp->rem1);
    log_table_t* res = log_table_init(
        NULL, -1, r1_fnum + array_size(&joinp->rem2), 0, t1->m.glb_values);

    int32_t i;
    log_value_t** tuple_values = calloc(sizeof(void*), res->num_fields);

    if (joinp->index2 == NULL) {
        SET_ALL(&t1->tuples, tuple1, log_tuple_t*)
            for (i = 0;i < r1_fnum;i++)
                tuple_values[i] = tuple1->values[
                                  ptr2i(array_get(&joinp->rem1, i))];

            SET_ALL(&t2->tuples, tuple2, log_tuple_t*)
                tblopr_combine_tuple(res, tuple1->count,
                    joinp, r1_fnum, tuple2, tuple_values);
            SET_END
        SET_END
    }

    else {
        int32_t t2_index = map_get_int(&t2->index_def, joinp->index2);
        int t1val_sz = array_size(&joinp->select1);
        log_value_t** t1val = calloc(sizeof(void*), t1val_sz);

        for (i = 0;i < t1val_sz;i++)
            t1val[i] = array_get(&joinp->select1, i);

        log_tuple_t* key_tuple = log_tuple_init_val(t1val, t1val_sz);
        log_tuple_t* match_tuples = log_index_get_index(
                                    t2, key_tuple, t2_index);

        free(t1val);
        log_tuple_free(key_tuple, t1->m.glb_values, false);

        SET_ALL(&t1->tuples, tuple1, log_tuple_t*)
            for (i = 0;i < r1_fnum;i++)
                tuple_values[i] = tuple1->values[
                                  ptr2i(array_get(&joinp->rem1, i))];

            /* join the value */
            INDEX_ALL(match_tuples, t2_index, tuple2)
                tblopr_combine_tuple(res, tuple1->count,
                        joinp, r1_fnum, tuple2, tuple_values);
            INDEX_END
        SET_END
    }

    free(tuple_values);
    return res; /* isEmpty? */
}

log_table_t*
log_tblopr_join(log_table_t* t1, log_table_t* t2, log_join_param_t* joinp)
{
    if (joinp->index2 != NULL &&
        !map_has(&t2->index_def, joinp->index2))
        log_table_add_index(t2, joinp->index2);

    if (joinp->full_join) return tblopr_full_join(t1, t2, joinp);
    else return tblopr_cond_join(t1, t2, joinp);
}

/* ==========================================================================
 * LOG ENGINE
 * ==========================================================================
 */

log_join_param_t*
log_join_param_init(log_join_param_t* jp, log_int_tuple_t* i2, set_t* gv)
{
    coll_alloc(&jp, sizeof(log_join_param_t), ENT_JOIN_PARAM, gv);

    jp->full_join = false;
    jp->index2 = i2;
    log_array_init(&jp->select1, KEY_ID(ENT_VALUE), 0, gv);
    log_array_init(&jp->select1i, KEY_ID(ENT_INT32), 0, gv);
    log_array_init(&jp->rem1, KEY_ID(ENT_INT32), 0, gv);
    log_array_init(&jp->rem2, KEY_ID(ENT_INT32), 0, gv);
    log_array_init(&jp->out_param, KEY_ID(ENT_INT32), 0, gv);
    return jp;
}

void
log_join_param_free(log_join_param_t* jp)
{
    log_array_free(&jp->select1);
    log_array_free(&jp->select1i);
    log_array_free(&jp->rem1);
    log_array_free(&jp->rem2);
    log_array_free(&jp->out_param);
    if (jp->index2 != NULL) log_int_tuple_free(jp->index2);
    coll_free_ptr(jp);
}

static array_t*
eng_get_cond_param(array_t* param)
{
    /* input and output are array of integer */

    int i;
    array_t* res =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, param->m.glb_values);
    for (i = 0;i < array_size(param);i++) {
        int32_t p = array_get_int(param, i);
        if (p >= 0) array_add(res, i2ptr(p));
    }
    return res;
}

static bool
eng_check_will_use(int32_t p, TYPE(array_t*, int32_t) not_used,
                   TYPE(array_t*, int32_t) reorder_list, log_rule_t* rule)
{
    int i;
    for (i = 0;i < array_size(not_used);i++) {
        if (ptr2i(array_get(not_used, i)) < 0) continue;

        array_t* a = (array_t*)array_get(&rule->param,
                     array_get_int(reorder_list, i));
        if (log_array_look_for(a, i2ptr(p)) >= 0) return true;
    }
    return false;
}

static bitset_t*
eng_gen_bitset(TYPE(array_t*, int32_t) inp)
{
    int i;
    bitset_t* b = log_bitset_init(NULL);

    for (i = 0;i < array_size(inp);i++) {
        int32_t idx = array_get_int(inp, i);
        if (idx >= 0) bitset_set(b, idx);
    }
    return b;
}

static int32_t
eng_get_joinable(log_rule_t* rule, TYPE(array_t*, int32_t) cur_param,
                 TYPE(array_t*, int32_t) table_sz,
                 TYPE(array_t*, int32_t) reorder)
{
    /* returns the seq id of the table to be joined. */

    int32_t i, tb_index;
    bitset_t* bitset1 = eng_gen_bitset(cur_param);

    for (i = 1;i < array_size(table_sz);i++) {

        if (ptr2i(array_get(table_sz, i)) < 0) continue;
        /* had joined */

        tb_index = ptr2i(array_get(reorder, i));

        bitset_t* bitset2 = eng_gen_bitset(array_get(&rule->param, tb_index));
        bitset_and(bitset2, bitset1);

        bool empty = bitset_empty(bitset2);
        log_bitset_free(bitset2);

        if (!empty) {
            log_bitset_free(bitset1);
            return i; /* cond join */
        }
    }

    log_bitset_free(bitset1);
    for (i = 1;i < array_size(table_sz);i++)
        if (ptr2i(array_get(table_sz, i)) >= 0) return i;
        /* full join */
    return -1;
}

static log_join_param_t*
eng_gen_join_param(TYPE(array_t*, int32_t) param1,
                        TYPE(array_t*, int32_t) param2,
                        TYPE(array_t*, int32_t) not_used,
                        TYPE(array_t*, int32_t) reorder,
                        log_rule_t* rule)
{
    /*
     * full join is false:
     * p1(7, 3, 2) p2(2, 3, -1, -3, 6) => outParam(7, 2, 6)
     * for join: select1(2, 1, v[-3]), index2(0, 1, 3)
     * for keep: rem1(0, 2), rem2(4)
     *
     * full join is true:
     * p1(7, 2, 6) p2(-4, 9, -1) => outParam(7, 2, 6, 9)
     * for join: select1(v[-4]), index2(0)
     * for keep: rem1(0, 1), rem2(1)
     */

    log_join_param_t* joinp = log_join_param_init(
        NULL, /*idx2*/NULL, rule->m.glb_values);

    TYPE(array_t*, int32_t) index2 =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, param1->m.glb_values);

    bitset_t* join_set = eng_gen_bitset(param1);
    bitset_t* param2_set = eng_gen_bitset(param2);

    int32_t i;
    bitset_and(join_set, param2_set);
    joinp->full_join = true;

    /* set select1 and index2 */
    for (i = 0;i < array_size(param2);i++) {
        int32_t p2 = array_get_int(param2, i);

        if (p2 < -1) {
            array_add(index2, i2ptr(i));
            log_value_t* v = (log_value_t*)
                             map_get(&rule->const_param, i2ptr(p2));
            array_add(&joinp->select1, v);
            array_add(&joinp->select1i, 0);
        }
        else if (p2 >= 0 && bitset_get(join_set, p2)) {
            int32_t pos1 = log_array_look_for(param1, i2ptr(p2));
            array_add(index2, i2ptr(i));

            array_add(&joinp->select1, NULL);
            array_add(&joinp->select1i, i2ptr(pos1));
            joinp->full_join = false;
        }
    }

    /* set rem1 */
    for (i = 0;i < array_size(param1);i++) {
        // if in left or right excluding processed tables, keep.
        int32_t p1 = array_get_int(param1, i);
        if (!eng_check_will_use(p1, not_used, reorder, rule)) continue;
        array_add(&joinp->rem1, i2ptr(i));
        array_add(&joinp->out_param, i2ptr(p1));
    }

    /* set rem2 */
    for (i = 0;i < array_size(param2);i++) {
        /*
         * excluding all join set (because it is included in param1)
         * if in left or right excluding processed tables, keep.
         */
        int32_t p2 = array_get_int(param2, i);
        if (p2 <= -1) continue;
        if (bitset_get(join_set, p2)) continue;
        if (!eng_check_will_use(p2, not_used, reorder, rule)) continue;

        array_add(&joinp->rem2, i2ptr(i));
        array_add(&joinp->out_param, i2ptr(p2));
    }

    /* void* ->int array not correct */
    int32_t sz2 = array_size(index2);
    joinp->index2 = sz2 > 0 ? log_int_tuple_init(index2) : NULL;

    log_array_free(index2);
    log_bitset_free(join_set);
    log_bitset_free(param2_set);
    return joinp;
}

log_engine_t*
log_eng_parse(const char* rules, set_t* gv)
{
    log_engine_t* eng = log_engine_init(NULL, gv);
    TYPE(map_t, array_t*) sem;

    log_sync_init(rules, gv);
    log_sync_parse(&sem);
    log_sem_process(&eng->rule_set, &sem);
    map_free(&sem);

    /* create tables */
    MAP_ALL(&eng->rule_set.param_size, rule)
        int32_t tsize = ptr2i(rule->value);
        if (map_has(&eng->rule_set.input_tables, rule->key) ||
            !map_has(&eng->rule_set.output_tables, rule->key))

            map_add(&eng->tables, rule->key,
                log_table_init(NULL, ptr2i(rule->key), tsize, 0, gv));
    MAP_END
    return eng;
}

static void
eng_check_tuples(log_engine_t* eng, log_table_t* table)
{
    /* check if tuple already present for add; or does not exist for remove.
     * the check is not good if there are multiple same items in the input.
     */

    bool is_remove = table->is_remove;
    log_table_t* org_table = map_get(&eng->tables, i2ptr(table->table_index));
    TYPE(array_t*, log_tuple_t*) to_be_removed = /* no ID to prevent free */
        log_array_init(NULL, 0, 0, table->m.glb_values);

    SET_ALL(&table->tuples, t, log_tuple_t*)
        log_tuple_t* ot = set_get(&org_table->tuples, t);
        if ((is_remove && ot == NULL) || (!is_remove && ot != NULL))
            array_add(to_be_removed, t);
            /*array_add(to_be_removed, ot); */
    SET_END

    ARRAY_ALL(to_be_removed, t, log_tuple_t*)
        /* log_table_remove(org_table, t); ?? */
        log_table_remove(table, t);
    ARRAY_END
    log_array_free(to_be_removed);
}

static void
eng_align_tables(log_engine_t* eng,
                 TYPE(array_t*, log_table_t*) inp_remove,
                 TYPE(array_t*, log_table_t*) inp_insert)
{
    TYPE(array_t*, int32_t) del_ids =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, eng->m.glb_values);
    TYPE(array_t*, int32_t) add_ids =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, eng->m.glb_values);

    ARRAY_ALL(inp_remove, tbl, log_table_t*)
        eng_check_tuples(eng, tbl);
        array_add(del_ids, i2ptr(tbl->table_index));
    ARRAY_END

    ARRAY_ALL(inp_insert, tbl, log_table_t*)
        eng_check_tuples(eng, tbl);
        array_add(add_ids, i2ptr(tbl->table_index));
    ARRAY_END

    log_sort_array(0, del_ids, inp_remove, NULL);
    log_sort_array(0, add_ids, inp_insert, NULL);

    int del_i, add_i;
    for (del_i = 0, add_i = 0;
        del_i < array_size(del_ids) || add_i < array_size(add_ids);) {

        bool align_add = false;
        bool align_del = false;

        if (del_i < array_size(del_ids) && add_i < array_size(add_ids)) {
            if (array_get(del_ids, del_i) ==
                array_get(add_ids, add_i)) {
                add_i++; del_i++; continue;
            }
            else if (array_get(del_ids, del_i) < array_get(add_ids, add_i))
                align_add = true;
            else align_del = true;
        }
        else if (del_i < array_size(del_ids)) align_add = true;
        else align_del = true;

        if (align_add) {
            log_table_t* org = array_get(inp_remove, del_i);
            log_table_t* dummy =
            log_table_init(NULL, org->table_index, org->num_fields,
                           0, eng->m.glb_values);

            array_ins(inp_insert, del_i, dummy);
            array_ins(add_ids, del_i, NULL);
            add_i++; del_i++;
        }

        if (align_del) {
            log_table_t* org = array_get(inp_insert, add_i);
            log_table_t* dummy =
            log_table_init(NULL, org->table_index, org->num_fields,
                           0, eng->m.glb_values);
            dummy->is_remove = true;

            array_ins(inp_remove, add_i, dummy);
            array_ins(del_ids, add_i, NULL);
            add_i++; del_i++;
        }
    }

    log_array_free(del_ids);
    log_array_free(add_ids);

    if (LOG_COMP) {
        char buf[2048]; int pos;
        pos = 0; pos = log_array_print(buf, pos, inp_remove, false);
        buf[pos] = 0; printf("[LOG] align_tbl - %s\n", buf);
        pos = 0; pos = log_array_print(buf, pos, inp_insert, false);
        buf[pos] = 0; printf("[LOG] align_tbl + %s\n", buf);
    }
}

static bool
eng_invoke_external(log_engine_t* eng, log_table_t* input,
                    log_table_t* del_output, log_table_t* add_output)
{
    /* delOutput and addOutput have the same table index */
    if (eng->ext_func == NULL) return false;
    return (*eng->ext_func)(eng, input, del_output, add_output);
}

void
log_eng_set_ext_func(log_engine_t* eng, void* func)
{
    eng->ext_func = func;
}

log_table_t*
log_get_table(log_engine_t* eng, const char* name)
{
    /* id is integer */
    void* id = map_get(&eng->rule_set.rule_index_map, (char*)name);
    return map_get(&eng->tables, id);
}

log_table_t*
log_get_org_table(log_engine_t* eng, log_table_t* t)
{
    return map_get(&eng->tables, i2ptr(t->table_index));
}

log_tuple_t*
log_query_on0(log_engine_t* eng, int32_t tid, log_value_t* value)
{
    /* USE INDEX_ALL to iterate on return value */
    log_tuple_t* qt = log_tuple_init(1);
    qt->values[0] = value;

    TYPE(array_t*, int32_t) ints =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, eng->m.glb_values);
    array_add(ints, 0);
    log_int_tuple_t* key0 = log_int_tuple_init(ints);
    log_array_free(ints);

    log_table_t* orgt = map_get(&eng->tables, i2ptr(tid));
    int32_t idx_i = log_table_add_index(orgt, key0);
    log_tuple_t* list = log_index_get_index(orgt, qt, idx_i);

    log_tuple_free(qt, eng->m.glb_values, true);
    log_int_tuple_free(key0);
    return list;
}

static TYPE(array_t*, log_table_t*)
eng_query_table(log_engine_t* eng, log_table_t* table,
                TYPE2(map_t*, int32_t, log_table_t*) all)
{
    /* the original value is in form of =value */

    set_t* gv = eng->m.glb_values;
    TYPE(array_t*, log_table_t*) res =
        log_array_init(NULL, 0 /* ENT_TABLE */, 0, gv);
    /* no type so free in log_eng_query will leave tables */

    int i, j;
    log_value_t** val = calloc(table->num_fields, sizeof(void*));
    log_table_t* org = map_get(all, i2ptr(table->table_index));

    SET_ALL(&table->tuples, tval, log_tuple_t*)
        TYPE(array_t*, int32_t) param =
            log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);

        for (i = j = 0;i < table->num_fields;i++) {
            /* NULL value only for query */
            if (tval->values[i] == NULL) continue;
            array_add(param, i2ptr(i));
            val[j++] = tval->values[i];
        }

        log_table_t* res_tbl = tblopr_query_table(org, param, val);
        array_add(res, res_tbl);
        log_array_free(param);
    SET_END

    free(val);
    return res;
}

TYPE(array_t*, log_table_t*)
log_eng_query(log_engine_t* eng, TYPE(array_t*, log_table_t*) input)
{
    TYPE(array_t*, log_table_t*) res =
    log_array_init(NULL, KEY_ID(ENT_TABLE), 0, eng->m.glb_values);

    TYPE(array_t*, log_table_t*) res1;

    ARRAY_ALL(input, table, log_table_t*)
        res1 = eng_query_table(eng, table, &eng->tables);
        ARRAY_ALL(res1, tbl, log_table_t*)
            array_add(res, tbl);
        ARRAY_END
        log_array_free(res1);
    ARRAY_END
    return res;
}

static int32_t
eng_get_table_index(log_rule_t* rule, int32_t param)
{
    return log_array_look_for(&rule->rule, i2ptr(param));
}

static int32_t
eng_search_tbl_in_rules(log_table_t* tbl,
                        TYPE(array_t*, log_table_t*) inp_tables)
{
    int idx = 0;
    ARRAY_ALL(inp_tables, t, log_table_t*)
        if (t->table_index == tbl->table_index) return idx;
        idx++;
    ARRAY_END
    return -1;
}

static log_table_t*
eng_reset_count(log_table_t* input)
{
    log_table_t* output = log_table_init(NULL, input->table_index,
        input->num_fields, input->tuples.size, input->m.glb_values);
    output->is_remove = input->is_remove;

    SET_ALL(&input->tuples, t, log_tuple_t*)
        log_tuple_t* tup = log_tuple_clone(t);
        tup->count = 1;
        log_table_add0(output, tup);
    SET_END
    return output;
}

static bool
eng_merge_output(log_engine_t* eng, TYPE(array_t*, int32_t) first_rule,
                 log_table_t* out_d_del, log_table_t* out_d_add,
                 TYPE(array_t*, log_table_t*) inp_del_tables,
                 TYPE(array_t*, log_table_t*) inp_add_tables)
{
    /* returns true if input table will be used later */

    if (LOG_COMP) {
        char buf[2048]; int pos;
        pos = 0; pos = log_table_print(buf, pos, out_d_del, false);
        buf[pos] = 0; printf("[LOG] merge_out - %s\n", buf);
        pos = 0; pos = log_table_print(buf, pos, out_d_add, false);
        buf[pos] = 0; printf("[LOG] merge_out + %s\n", buf);
    }

    if (table_size(out_d_del) == 0 && table_size(out_d_add) == 0)
        return false;

    int32_t ipos = eng_search_tbl_in_rules(out_d_del, inp_del_tables);
    if (ipos >= 0) {
        tblopr_merge_delta(out_d_del,
            array_get(inp_del_tables, ipos), array_get(inp_add_tables, ipos));
        tblopr_merge_delta(out_d_add,
            array_get(inp_add_tables, ipos), array_get(inp_del_tables, ipos));
        return false;
    }

    int32_t new_inp_no =
        map_has(&eng->rule_set.output_tables, i2ptr(out_d_del->table_index))
        ? 1000000 : /* just a big number */
        array_get_int(map_get(&eng->rule_set.table_rule_map,
                      i2ptr(out_d_del->table_index)), 0);
    log_insert_item(new_inp_no, first_rule,
        out_d_del, out_d_add, inp_del_tables, inp_add_tables);
    return true;
}

void
log_eng_do_union(log_engine_t* eng, log_table_t* input, log_table_t* output)
{
    /* example: (0, 1, 2) > (2, 1, -, 'const', 0), (0, -, 'aa', 2, 1) */

    log_rule_t* rule = map_get(&eng->rule_set.rules,
                               i2ptr(output->table_index));

    tblopr_match_reorder_and_merge(input, output,
      array_get(&rule->param, eng_get_table_index(rule, input->table_index)),
      array_get(&rule->param, eng_get_table_index(rule, output->table_index)),
      &rule->const_param);
}

void
log_eng_do_join(log_engine_t* eng, log_table_t* input, log_table_t* output)
{
    /*
     * example: (7, 6, 2) : (7, 3, -1, -2, 2), (2, 3, -1, -3, 6)
     * initial process: (7, 3, -1, -2, 2) => (7, 3, 2)
     *   drop 'ignored' param, match constants and merge identical;
     * repeated joins - with condition having a higher priority than
     *  full join, possible with constants; the first join could be self join.
     * final process: reorder based on left (7, 6, 2)
     * intermediate tables are not hash table, just list?
     *
     * join in the order of table size, smallest first
     * table size -1 indicates it had been joined before
     */
    set_t* gv = eng->m.glb_values;

    log_rule_t* rule = map_get(&eng->rule_set.rules,
                               i2ptr(output->table_index));

    TYPE(array_t*, int32_t) table_sz =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);
    TYPE(array_t*, int32_t) rule_reorder =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv); /* remove later */
    TYPE(array_t*, int32_t) natural_order =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);

    /* STEP 0: sort based on table size and get the first join pair */
    array_add(table_sz, 0);
    array_add(natural_order, 0);
    array_add(rule_reorder, array_get(&rule->rule, 0));

    int i;
    for (i = 1;i < array_size(&rule->rule);i++) {
        int32_t p = array_get_int(&rule->rule, i);
        array_add(table_sz, i2ptr(
                  table_size((log_table_t*)map_get(&eng->tables,
                  i2ptr(p)))));
        array_add(natural_order, i2ptr(i));
        array_add(rule_reorder, i2ptr(p));
    }

    /* 1 for skip left rule */
    log_sort_array(1, table_sz, rule_reorder, natural_order);

    /* STEP 1: merge, reorder and merge for the input. */
    log_table_t* table1 = NULL;
    TYPE(array_t*, int32_t) param1 = NULL;
    int32_t join1_idx = log_array_look_for(rule_reorder,
            i2ptr(input->table_index));

    if (join1_idx < array_size(rule_reorder) - 1 && input->table_index ==
        array_get_int(rule_reorder, join1_idx + 1)) {
        /*
         * do self join. only one self join is supported as more will need
         * full table join and less efficient - use intermediate table instead
         * for this case.
         * Example: X(b, a, c) : x(a, b, 'v', -, c) x(b, 'w', -, a, c)
         */

        array_set(table_sz, join1_idx, i2ptr(-1)); /* mark as used */
        array_set(table_sz, join1_idx + 1, i2ptr(-1)); /* mark as used */

        /* pos based on rule sequence */
        int pos1 = log_array_look_for(&rule->rule, i2ptr(input->table_index));
        int pos2 = log_array_look_for(&rule->rule,
                   i2ptr(input->table_index)) + 1;

        TYPE(array_t*, int32_t) param1Org = array_get(&rule->param, pos1);
                                /* (a, b, 'v', -, c) */
        TYPE(array_t*, int32_t) param2Org = array_get(&rule->param, pos2);
                                /* (b, 'w', -, a, c) */
                                param1 = eng_get_cond_param(param1Org);
                                /* (a, b, c) */
        TYPE(array_t*, int32_t) param2 = eng_get_cond_param(param2Org);
                                /* (b, a, c) */

        log_table_t* table0 = map_get(&eng->tables,
                                      i2ptr(input->table_index));

                                /* original table */
                     table1 = log_table_init(
                              NULL, -1, array_size(param1), 0, gv);
        log_table_t* table2 = log_table_init(
                              NULL, -1, array_size(param1), 0, gv);

        tblopr_match_reorder_and_merge(
                        input, table1, param1Org, param1, &rule->const_param);
        tblopr_match_reorder_and_merge(
                        input, table2, param2Org, param2, &rule->const_param);

        log_join_param_t* joinp1 = eng_gen_join_param(
                        param1, param2Org, table_sz, natural_order, rule);
        log_join_param_t* joinp2 = eng_gen_join_param(
                        param2, param1Org, table_sz, natural_order, rule);

        log_table_t* out_tb1 = log_tblopr_join(table1, table0, joinp1);
                                /* outp: (a, b, c) */
        log_table_t* out_tb2 = log_tblopr_join(table1, input, joinp1);
                                /* outp: (a, b, c) */
        log_table_t* out_tb3 = log_tblopr_join(table2, table0, joinp2);
                                /* outp: (b, a, c) */

        /* reorder outTb3, it should only differ in order with outTb1, 2. */
        TYPE(array_t*, int32_t) reorder =
            log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);

        ARRAY_ALL_INT(&joinp1->out_param, pos)
            array_add(reorder, i2ptr(
                      log_array_look_for(&joinp2->out_param, i2ptr(pos))));
        ARRAY_END

        log_table_t* out_tb4 =
                log_table_init(NULL, -1, out_tb3->num_fields, 0, gv);
        tblopr_reorder_table(out_tb3, reorder, NULL, out_tb4);

        /* merge outTb1, 2, and 4 */
        log_table_free(table1);
        table1 = log_table_init(NULL, -1, out_tb1->num_fields, 0, gv);

        tblopr_merge_table(out_tb1, table1, false);
        tblopr_merge_table(out_tb4, table1, false);
        tblopr_merge_table(out_tb2, table1, input->is_remove);

        log_array_free(param1);
        param1 = log_array_clone(&joinp1->out_param);

        log_table_free(table2);
        log_table_free(out_tb1);
        log_table_free(out_tb2);
        log_table_free(out_tb3);
        log_table_free(out_tb4);

        log_array_free(reorder);
        log_array_free(param2);
        log_join_param_free(joinp1);
        log_join_param_free(joinp2);
    }
    else {
        int32_t pos1 = log_array_look_for(&rule->rule,
                                          i2ptr(input->table_index));
        TYPE(array_t*, int32_t) param1_org = array_get(&rule->param, pos1);
        param1 = eng_get_cond_param(param1_org);

        table1 = log_table_init(NULL, -1, array_size(param1), 0, gv);
        tblopr_match_reorder_and_merge(
            input, table1, param1_org, param1, &rule->const_param);
        array_set(table_sz, join1_idx, i2ptr(-1)); /* mark as used */
    }

    /* STEP 2: repeated join, first condition join, then full join */
    for (;;) { /* join loop, the iteration param is param1 and table1 */

        int32_t	join2_idx = eng_get_joinable(
            rule, param1, table_sz, natural_order);

        if (join2_idx < 0) break; /* nothing to join */
        array_set(table_sz, join2_idx, i2ptr(-1)); /* mark as used */

        log_table_t* table2 = map_get(
            &eng->tables, array_get(rule_reorder, join2_idx));
        TYPE(array_t*, int32_t) param2 = array_get(&rule->param,
            array_get_int(natural_order, join2_idx));

        log_join_param_t* joinp =
            eng_gen_join_param(param1, param2, table_sz, natural_order, rule);
        log_table_t* table1n = log_tblopr_join(table1, table2, joinp);

        log_table_free(table1);
        log_array_free(param1);

        param1 = log_array_clone(&joinp->out_param);
        log_join_param_free(joinp);
        table1 = table1n;
    }

    /* STEP 3: reorder the final table */
    TYPE(array_t*, int32_t) final_order =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);
    ARRAY_ALL_INT((array_t*)array_get(&rule->param, 0), p)
        if (p < -1) array_add(final_order, i2ptr(p));
        else array_add(final_order,
                       i2ptr(log_array_look_for(param1, i2ptr(p))));
    ARRAY_END

    tblopr_reorder_table(table1, final_order, &rule->const_param, output);
    output->is_remove = input->is_remove;

    log_table_free(table1);
    log_array_free(param1);

    log_array_free(table_sz);
    log_array_free(rule_reorder);
    log_array_free(natural_order);
    log_array_free(final_order);
}

/*
 * the basic assumption about external function (and all) is that the result
 * of left side does not depend on the order of application of delta change
 * of the tables from right side. since the original input table could be
 * obtained in the function, the computation could rely on delta(preferable
 * for performance) or whole set, but C=A\B still could not be computed
 * because order of delta application is relevant.
 *
 * the computation order is based on topology sort, and guarantees that each
 * rule will only be applied once, e.g., C:A, B; D:C. Assume the input
 * contains A and B, D will be computed only if both A and B have been
 * applied on C.
 *
 * when input tables are checked (no adding to existing tuple, and no removing
 * of none existing tuple, and adding does not overlap with removing), the
 * order of adding and removing is not relevant. inpDelTables applied before
 * inpAddTables is due to performance consideration. (not validated yet)
 *
 * tuples in right always regarded as having count 1
 * tuples in left has actual count.
 *
 * inpDelTables and inpAddTables must be paired, i.e.,
 * delTables[i].id == addTables[i].id holds for all i.
 */

static void
eng_delta0(log_engine_t* eng, TYPE(array_t*, log_table_t*) inp_del_tables,
               TYPE(array_t*, log_table_t*) inp_add_tables,
               TYPE2(map_t*, int32_t, log_table_t*) del_out_tables,
               TYPE2(map_t*, int32_t, log_table_t*) add_out_tables)
{
    /* input tables will be destroyed, but still need to free it */
    set_t* gv = eng->m.glb_values;

    TYPE(array_t*, int32_t) first_rule =
        log_array_init(NULL, KEY_ID(ENT_INT32), 0, eng->m.glb_values);

    ARRAY_ALL(inp_del_tables, table, log_table_t*)
        int32_t v = array_get_int( // item 0 is smallest in each set
            map_get(&eng->rule_set.table_rule_map,
            i2ptr(table->table_index)), 0);

        array_add(first_rule, i2ptr(v));
    ARRAY_END

    /* there might be tie in sort. just pick from the initial order */
    log_sort_array(0, first_rule, inp_del_tables, inp_add_tables);

    while (array_size(inp_del_tables) > 0) {
        /* inpDTables always has 1 as count but outDTable will has actual
         * count before turning into inpDTables. Final output tables will
         * have actual count.
         */

        array_rmv(first_rule, 0);
        /* D stands for delta */
        log_table_t* inp_d_del_table = array_rmv(inp_del_tables, 0);
        log_table_t* inp_d_add_table = array_rmv(inp_add_tables, 0);
        int32_t inp_table_id = inp_d_del_table->table_index;

        if (LOG_COMP) {
            char buf[2048]; int pos;
            pos = 0; pos = log_table_print(buf, pos, inp_d_del_table, false);
            buf[pos] = 0; printf("[LOG] delta - %s\n", buf);
            pos = 0; pos = log_table_print(buf, pos, inp_d_add_table, false);
            buf[pos] = 0; printf("[LOG] delta + %s\n", buf);
        }

        if (map_has(&eng->rule_set.output_tables, i2ptr(inp_table_id))) {
            if (table_size(inp_d_del_table) > 0)
                map_add(del_out_tables, i2ptr(inp_table_id), inp_d_del_table);
            else log_table_free(inp_d_del_table);

            if (table_size(inp_d_add_table) > 0)
                map_add(add_out_tables, i2ptr(inp_table_id), inp_d_add_table);
            else log_table_free(inp_d_add_table);
            continue;
        }

        if (!map_has(&eng->rule_set.input_tables, i2ptr(inp_table_id))) {
            tblopr_gen_delta(inp_d_del_table,
                             map_get(&eng->tables, i2ptr(inp_table_id)));
            tblopr_gen_delta(inp_d_add_table,
                             map_get(&eng->tables, i2ptr(inp_table_id)));
        }

        if (table_size(inp_d_del_table) == 0 &&
            table_size(inp_d_add_table) == 0) {
            log_table_free(inp_d_del_table);
            log_table_free(inp_d_add_table);
            continue;
        }

        log_table_t* inp_d_del_table_c1 = eng_reset_count(inp_d_del_table);
        log_table_t* inp_d_add_table_c1 = eng_reset_count(inp_d_add_table);

        TYPE(array_t*, int32_t) rule_order =
                map_get(&eng->rule_set.table_rule_map, i2ptr(inp_table_id));

        ARRAY_ALL_INT(rule_order, rule_no)
            log_rule_t* rule = map_get(&eng->rule_set.rules, i2ptr(rule_no));

            log_table_t* out_d_del_table = log_table_init(0, rule_no,
                    map_get_int(&eng->rule_set.param_size,
                    i2ptr(rule_no)), 0, gv);

            log_table_t* out_d_add_table = log_table_init(0, rule_no,
                    map_get_int(&eng->rule_set.param_size,
                    i2ptr(rule_no)), 0, gv);

            out_d_del_table->is_remove = true;
            if (eng_invoke_external
                (eng, inp_d_del_table_c1, out_d_del_table, out_d_add_table)) {
                bool keep = eng_merge_output(eng, first_rule, out_d_del_table,
                 out_d_add_table, inp_del_tables, inp_add_tables);

                if (!keep) {
                    log_table_free(out_d_del_table);
                    log_table_free(out_d_add_table);
                }

                out_d_del_table = log_table_init(0, rule_no,
                    map_get_int(&eng->rule_set.param_size,
                            i2ptr(rule_no)), 0, gv);

                out_d_add_table = log_table_init(0, rule_no,
                    map_get_int(&eng->rule_set.param_size,
                            i2ptr(rule_no)), 0, gv);

                out_d_del_table->is_remove = true;
                eng_invoke_external
                  (eng, inp_d_add_table_c1, out_d_del_table, out_d_add_table);
                /* will also merge below */
            }
            else if (rule->is_union) {
                log_eng_do_union(eng, inp_d_del_table_c1, out_d_del_table);
                log_eng_do_union(eng, inp_d_add_table_c1, out_d_add_table);
            }
            else {
                log_eng_do_join(eng, inp_d_del_table_c1, out_d_del_table);
                log_eng_do_join(eng, inp_d_add_table_c1, out_d_add_table);
            }

            bool keep = eng_merge_output(eng, first_rule, out_d_del_table,
                out_d_add_table, inp_del_tables, inp_add_tables);

            if (!keep) {
                log_table_free(out_d_del_table);
                log_table_free(out_d_add_table);
            }
        ARRAY_END /* for all rules related to one table input */

        /* merge input table */
        tblopr_final_delta(inp_d_del_table,
            map_get(&eng->tables, i2ptr(inp_d_del_table->table_index)));
        tblopr_final_delta(inp_d_add_table,
            map_get(&eng->tables, i2ptr(inp_d_add_table->table_index)));

        log_table_free(inp_d_del_table_c1);
        log_table_free(inp_d_add_table_c1);
        log_table_free(inp_d_del_table);
        log_table_free(inp_d_add_table);
    } /* for all inputs */

    log_array_free(first_rule);
}

TYPE(array_t*, log_table_t*)
log_eng_delta(log_engine_t* eng, TYPE(array_t*, log_table_t*) inp_remove,
              TYPE(array_t*, log_table_t*) inp_insert)
{

    set_t* gv = eng->m.glb_values;
    /* no VALUE_ID so that tables will not be freed */
    TYPE2(map_t*, int32_t, log_table_t*) del_output =
            map_init(NULL, KEY_ID(ENT_INT32), 0, gv);
    TYPE2(map_t*, int32_t, log_table_t*) add_output =
            map_init(NULL, KEY_ID(ENT_INT32), 0, gv);

    eng_align_tables(eng, inp_remove, inp_insert);
    eng_delta0(eng, inp_remove, inp_insert, del_output, add_output);

    TYPE(array_t*, log_table_t*) all =
        log_array_init(NULL, KEY_ID(ENT_TABLE), 0, gv);
    MAP_ALL(del_output, tn) array_add(all, tn->value); MAP_END
    MAP_ALL(add_output, tn) array_add(all, tn->value); MAP_END

    /* reset state */
    eng_invoke_external(eng, NULL, NULL, NULL);
    map_free(del_output);
    map_free(add_output);
    return all;
}

/* ==========================================================================
 * SERIALIZATION
 * ==========================================================================
 */

log_table_t*
log_io_table_name_reset(log_engine_t* eng, const char* name)
{
    set_t* gv = eng->m.glb_values;
    log_value_t* table_name = log_value_init(name, 0, gv);
    map_node_t* node = log_hash_get(
                       &eng->rule_set.rule_index_map, table_name);

    log_value_free(table_name, eng->m.glb_values);
    if (node == NULL) return NULL;

    void* tbl_idx = node->value; /* int32_t */
    int32_t tbl_fd = map_get_int(&eng->rule_set.param_size, tbl_idx);
    log_table_t* tbl = log_table_init(NULL, ptr2i(tbl_idx), tbl_fd, 0, gv);
    return tbl;
}

bool
log_io_parse_line(const char* line, log_engine_t* eng, bool use_null,
               TYPE(array_t*, log_table_t*) inp_remove,
               TYPE(array_t*, log_table_t*) inp_insert)
{
    static int32_t line_type = 0; /* 1 for add; 2 for delete */
    static int32_t line_rm = 0;
    static log_table_t* cur_tbl;

    if (line == NULL) {
        line_type = 0;
        return true;
    }

    set_t* gv = eng->tables.m.glb_values;
    if (line_type == 0) {
        char type;
        char buf[512];

        int32_t f = sscanf(line, "%c:%d:%s", &type, &line_rm, buf);
        if (f != 3) return false;
        if (type == '+') line_type = 1;
        else if (type == '-') line_type = 2;
        else return false;
        if (line_rm <= 0) return false;

        log_table_t* tbl = log_io_table_name_reset(eng, buf);
        if (tbl == NULL) return false;

        if (line_type == 1) array_add(inp_insert, tbl);
        else array_add(inp_remove, tbl);
        if (line_type == 2) tbl->is_remove = true;
        cur_tbl = tbl;
        return true;
    }

    if (line_rm-- == 0) return false;
    if (line_rm == 0) line_type = 0;

    log_tuple_t* tpl = use_null ?
        log_tuple_init_str_null(line, ':', gv) :
        log_tuple_init_str(line, ':', gv);

    log_table_add(cur_tbl, tpl);
    return true;
}

int32_t
log_io_gen_line(char* text, int pos, log_engine_t* eng,
             TYPE(array_t*, log_table_t*) all)
{
    ARRAY_ALL(all, tbl, log_table_t*)
        int32_t tbl_idx = tbl->table_index;
        log_value_t* tbl_name = map_get(
                                &eng->rule_set.rule_name_map, i2ptr(tbl_idx));
        pos += sprintf(text + pos, "%c:%d:%s\n", tbl->is_remove ? '-' : '+',
            table_size(tbl), tbl_name->value.a);

        SET_ALL(&tbl->tuples, tuple, log_tuple_t*)
            pos = log_tuple_print(text, pos, tuple);
            text[pos++] = '\n';
        SET_END
    ARRAY_END
    return pos;
}

/* ==========================================================================
 * PUBLIC API
 * ==========================================================================
 */

void*
datalog_init(const char* rules, void* func)
{
    /* will call exit in case rules are incorrect */
    set_t* gv = set_init(NULL, 0, 0, NULL);
    log_set_global_value(gv);
    log_engine_t* eng = log_eng_parse(rules, gv);
    log_eng_set_ext_func(eng, func);

    eng->io.inp_insert = NULL;
    eng->io.inp_remove = NULL;
    eng->io.res = NULL;
    return eng;
}

void
datalog_free(void* e)
{
    log_engine_t* eng = e;
    set_t* gv = eng->tables.m.glb_values;
    log_engine_free(eng);
    set_free(gv);
}

bool
datalog_put_table(void* e, bool is_remove, const char* name)
{
    /* each table must only appear at most twice - add / remove */

    log_engine_t* eng = e;
    set_t* gv = eng->tables.m.glb_values;

    log_table_t* tbl = log_io_table_name_reset(eng, name);
    if (tbl == NULL) return false;

    if (eng->io.inp_insert == NULL || eng->io.inp_remove == NULL) {
        eng->io.inp_remove = log_array_init(NULL, ENT_TABLE, 0, gv);
        eng->io.inp_insert = log_array_init(NULL, ENT_TABLE, 0, gv);
    }

    tbl->is_remove = is_remove;
    eng->io.cur_tbl = tbl;
    eng->io.cur_tuple = NULL;
    if (is_remove) array_add(eng->io.inp_remove, tbl);
    else array_add(eng->io.inp_insert, tbl);
    return true;
}

void
datalog_put_field(void* e, void* value, int32_t len)
{
    /* value is treated as c-str if len is zero */

    log_engine_t* eng = e;
    set_t* gv = eng->tables.m.glb_values;
    int n_fd = eng->io.cur_tbl->num_fields;

    if (eng->io.cur_tuple == NULL) {
        eng->io.cur_tuple = log_tuple_init(n_fd);
        eng->io.cur_tuple->count = 1;
        eng->io.t_idx = 0;
    }

    eng->io.cur_tuple->values[eng->io.t_idx++] =
        value == NULL ? NULL : log_value_init(value, len, gv);

    if (eng->io.t_idx >= n_fd) {
        log_tuple_set_hash_code(eng->io.cur_tuple, n_fd);
        log_table_add(eng->io.cur_tbl, eng->io.cur_tuple);
        eng->io.cur_tuple = NULL;
    }
}

void
datalog_opr(void* e, bool query)
{
    log_engine_t* eng = e;
    if (query) {
        /* must provide one tuple in inp_insert table */
        ovs_assert(array_size(eng->io.inp_insert) == 1 &&
            array_size(eng->io.inp_remove) == 0);

        eng->io.res = log_eng_query(eng, eng->io.inp_insert);
    }
    else {
        ovs_assert(eng->io.res == NULL &&
            eng->io.inp_insert != NULL && eng->io.inp_remove != NULL);

        eng->io.res = log_eng_delta(eng,
            eng->io.inp_remove, eng->io.inp_insert);
    }

    log_array_free(eng->io.inp_remove);
    log_array_free(eng->io.inp_insert);
    eng->io.inp_remove = NULL;
    eng->io.inp_insert = NULL;
    eng->io.t_idx = 0;
}

bool
datalog_get_table(void* e, bool* is_remove, const char** name,
                 int32_t* n_tuples, int32_t* n_fields)
{
    /* return false if there is no more table */
    log_engine_t* eng = e;

    if (eng->io.t_idx >= array_size(eng->io.res)) {
        log_array_free(eng->io.res);
        eng->io.res = NULL;
        return false;
    }

    eng->io.cur_tbl = array_get(eng->io.res, eng->io.t_idx++);
    *is_remove = eng->io.cur_tbl->is_remove;
    *n_tuples = table_size(eng->io.cur_tbl);
    *n_fields = eng->io.cur_tbl->num_fields;

    log_value_t* val = map_get(
        &eng->rule_set.rule_name_map, i2ptr(eng->io.cur_tbl->table_index));
    *name = val->value.a;

    eng->io.hash_node = NULL;
    eng->io.hash_b = 0;
    eng->io.f_idx = eng->io.cur_tbl->num_fields;
    return true;
}

bool
datalog_get_field(void* e, void* res, int32_t* sz)
{
    /* return false if switches to another table */

    void** v = (void**)res;
    log_engine_t* eng = e;
    int n_fd = eng->io.cur_tbl->num_fields;

    if (eng->io.f_idx < n_fd) {
        log_value_t* val = eng->io.cur_tuple->values[eng->io.f_idx++];
        *v = val->value.a;
        *sz = val->size;
        return true;
    }

    bool r = log_hash_next(&eng->io.cur_tbl->tuples,
        &eng->io.hash_b, &eng->io.hash_node);
    if (!r) return false;

    eng->io.f_idx = 0;
    eng->io.cur_tuple = eng->io.hash_node->key;
    log_value_t* val = eng->io.cur_tuple->values[eng->io.f_idx++];

    *v = val->value.a;
    *sz = val->size;
    return true;
}

/*
 * TODO: add stats to value, hash, and table operation.
 */

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
#include "ovstest.h"
#include "ovn/lib/datalog.h"
#include "ovn/lib/datalog-private.h"

static int32_t log_tst_no_cases_total = 0;
static int32_t log_tst_no_cases_failed = 0;

static void
t_assert(bool r, const char* s)
{
    log_tst_no_cases_total++;
    if (r) return;
    log_tst_no_cases_failed++;
    printf("FAILED: %s\n",s);
}

static void
t_assert1(bool r, const char* s)
{
    if (r) return;
    printf("FAILED: %s\n",s);
}

static void
t_sum(void)
{
    printf("  test result %d/%d failed\n",
    log_tst_no_cases_failed, log_tst_no_cases_total);
}

/* ==========================================================================
 * TEST CASES
 * ==========================================================================
 */

struct test_align_s {
    int32_t a;
    /*char b; */
    void* c[0];
};

static void
gen_str(char* p, int32_t len)
{
    int32_t i;
    for (i = 0;i < len;i++) *p++ = (random() % 52) + 65;
    *p++ = 0;
}

static void
test_collections(void)
{
    char buf[1024];
    {
        /* null will be printed. */
        char* p = NULL;
        printf("- hello log %s\n", p);

        struct test_align_s s;
        printf(
        "- size of types\n  %p char(%lu) int(%lu) "
        "long(%lu) llong(%lu) %d %d\n",
            &s, sizeof(char), sizeof(int), sizeof(long), sizeof(long long),
            0 /* (int)((char*)(&s.b) - (char*)(&s.a)) */,
            (int)((char*)s.c - (char*)(&s.a)));

        t_assert(sizeof(void*) >= sizeof(int32_t), "holding int in ptr");
        /* nested variable with same name */
        int i; for (i = 0;i < 5;i++) {
            int i; for (i = 0;i < 5;i++) {
            }
        }
    }

    { /* check integer could be stored as pointer */
        void* p1;
        void* p2;

        int i;
        char* c1 = (char*)&p1;
        char* c2 = (char*)&p2;
        for (i = 0;i < sizeof(void*);i++) {
            c1[i] = 0x07; c2[i] = 0x70;
        }
        printf("  int as ptr %p %p\n", p1, p2);

        p1 = 0; p2 = 0;
        printf("  int as ptr %p %p\n", p1, p2);
        t_assert(p1 == p2, "int as ptr, compare 0 error");
        t_assert(ptr2i(p1) == 0, "int as ptr, int 0 error");

        p1 = i2ptr(-1); p2 = i2ptr(-1);
        printf("  int as ptr %p %p\n", p1, p2);
        t_assert(p1 == p2, "int as ptr, compare -1 error");
        t_assert(ptr2i(p2) == -1, "int as ptr, int -1 error");
        printf("- int as ptr\n");
    }

    { /* check bitset */
        bitset_t* bs = log_bitset_init(NULL);
        bitset_t* bs1 = log_bitset_init(NULL);

        t_assert(bs->size == 0, "bitmap, init size not 0");
        bitset_set(bs, 0);
        bitset_set(bs, 31);
        t_assert(bs->size == 1, "bitmap, size not 1 after set bit 31");
        bitset_set(bs, 32);
        t_assert(bs->size == 2, "bitmap, size not 2 after set bit 32");

        t_assert(bitset_get(
            bs, 0) && bitset_get(bs, 31) && bitset_get(bs, 32),
            "bitmap, not set on bit 0, 31, 32");

        bitset_set(bs1, 64);
        bitset_set(bs1, 31);
        bitset_and(bs, bs1);
        t_assert(!bitset_empty(bs) && !bitset_get(bs, 0) &&
            bitset_get(bs, 31) && !bitset_get(bs, 32) && bs->size == 2,
            "bitmap, AND failed");

        log_bitset_free(bs);
        log_bitset_free(bs1);
        printf("- bitmap\n");
    }

    { /* check array */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        int i;
        array_t ary1;
        array_t* ary2;
        log_array_init(&ary1, 0, 0, gv);
        ary2 = log_array_init(NULL, 0, 5, gv);

        for (i = 0;i < 6;i++) {
            array_add(ary2, i2ptr(i));
            array_add(&ary1, i2ptr(i * 10));
        }
        t_assert(ary2->len == 10, "array realloc failed");
        array_set(ary2, 2, i2ptr(20));
        t_assert(ptr2i(array_get(ary2, 1)) == 1 &&
                 ptr2i(array_get(ary2, 5)) == 5 &&
                 ptr2i(array_get(ary2, 2)) == 20,
                 "array get or set failed");

        array_ins(&ary1, 0, i2ptr(1));
        array_ins(&ary1, 1, i2ptr(2));
        array_ins(&ary1, 8, i2ptr(100));
        int32_t v = ptr2i(array_rmv(&ary1, 3));
        t_assert(v == 10, "array insert and remove failed");
        t_assert(array_size(&ary1) == 8, "array size failed");
        t_assert(log_array_look_for(&ary1, i2ptr(100)) == 7,
                 "array look for failed");

        ARRAY_ALL_INT(&ary1, i)
            printf("   %d ", i);
            if (i == 40) ARRAY_EXIT;
        ARRAY_END
        log_array_free(&ary1);
        log_array_free(ary2);
        set_free(gv);
        printf("\n- array\n");
    }

    { /* check hash code for string, int. check map */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        int32_t l1 = 0, l2 = 0;
        int32_t c1 = log_hash_code_byte("hello", &l1);
        int32_t c2 = log_hash_code_byte("world ", &l2);
        printf("  hash code len(%d) %x len(%d) %x\n", l1, c1, l2, c2);
        t_assert(l1 == 5 && l2 == 6, "hash code len");

        map_t* map1 = map_init(
            NULL, KEY_ID(ENT_INT32) | VALUE_ID(ENT_INT32), 11, gv);
        /* all on same slot */
        map_add(map1, i2ptr(5), i2ptr(6));
        map_add(map1, i2ptr(16), i2ptr(17));
        map_add(map1, i2ptr(27), i2ptr(28));

        t_assert(ptr2i(map_get(map1, i2ptr(5))) == 6 &&
                 ptr2i(map_get(map1, i2ptr(16))) == 17 &&
                 ptr2i(map_get(map1, i2ptr(27))) == 28 &&
                 map_size(map1) == 3,
            "map size, get, or set");

        t_assert(map1->len == 11, "map int 0");
        int sz = 0;
        sz = log_hash_print(buf, sz, map1, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27->28,16->17,5->6}") == 0, "map int 1");

        /* check link operation */
        t_assert(ptr2i(map_del(map1, i2ptr(16))) == 17, "map int 2");
        sz = 0; sz = log_hash_print(buf, sz, map1, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27->28,5->6}") == 0, "map int 3");

        t_assert(ptr2i(map_del(map1, i2ptr(5))) == 6, "map int 4");
        sz = 0; sz = log_hash_print(buf, sz, map1, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27->28}") == 0, "map int 5");

        map_add(map1, i2ptr(5), i2ptr(6));
        sz = 0; sz = log_hash_print(buf, sz, map1, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{5->6,27->28}") == 0, "map int 6");
        t_assert(ptr2i(map_del(map1, i2ptr(5))) == 6, "map int 7");
        sz = 0; sz = log_hash_print(buf, sz, map1, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27->28}") == 0, "map int 8");

        t_assert(ptr2i(map_del(map1, i2ptr(27))) == 28, "map int 9");
        sz = 0; sz = log_hash_print(buf, sz, map1, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{}") == 0 && map_size(map1) == 0, "map int 10");

        /* break in map */
        int32_t i = 0;
        map_add(map1, i2ptr(77), i2ptr(66));
        map_add(map1, i2ptr(33), i2ptr(55));
        map_add(map1, i2ptr(77), i2ptr(88));
        t_assert(map_has(map1, i2ptr(33)), "map int 11a");

        t_assert(ptr2i(map_get(map1, i2ptr(77))) == 88 &&
                 map_size(map1) == 2, "map int 11");

        MAP_ALL(map1, node)
            node++; /* make no warning */
            i++;
            MAP_EXIT;
        MAP_END
        t_assert(i == 1, "map int 12");

        /* map rehash */
        for (i = 0;i < 8192;i++)
            map_add(map1, i2ptr(i), i2ptr(i * 2));

        printf("  map len = %d size = %d\n", map1->len, map1->size);
        t_assert(map_size(map1) == 8192, "map int 13");
        for (i = 0;i < 8192;i++)
            t_assert1(ptr2i(map_get(map1, i2ptr(i))) == i * 2,
                      "map set/get 14");

        for (i = 0;i < 8192;i++)
            t_assert1(ptr2i(map_del(map1, i2ptr(i))) == i * 2,
                      "map set/get 15");
        printf("  map len = %d size = %d\n", map1->len, map1->size);
        t_assert(map_size(map1) == 0, "map int 16");

        map_free(map1);
        set_free(gv);
        printf("- map, int and string\n");
    }

    { /* check set on string */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        set_t set1;
        set_init(&set1, KEY_ID(ENT_STR), 0, gv);
        char* app1 = "apple";
        char* app2 = malloc(strlen(app1) + 1);
        strcpy(app2, app1);
        t_assert(app1 != app2, "two apple string");

        set_add(&set1, app1);
        set_add(&set1, app2);
        set_add(&set1, "cherry");
        set_add(&set1, "kiwi");
        // test_hash_dump(&set1);

        t_assert(set_has(&set1, app1) && set_has(&set1, app2) &&
            set_get(&set1, app2) == app1 &&
            set_size(&set1) == 3, "right apple");

        int i = 0;
        SET_ALL(&set1, node, const char*)
            node++; /* make no warning */
            i++;
            SET_EXIT;
        SET_END
        t_assert(i == 1, "set exit");

        /* check set remove */
        set_t* set2 = set_init(NULL, KEY_ID(ENT_INT32), 11, gv);
        t_assert(set2->len == 11, "set int 1");

        set_add(set2, i2ptr(5));
        set_add(set2, i2ptr(16));
        set_add(set2, i2ptr(27));
        // test_hash_dump(set2);
        int sz = 0;
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27,16,5}") == 0, "set int 1");

        SET_ALL_INT(set2, node)
            if (node == 16) SET_REMOVE_ITEM;
        SET_END
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27,5}") == 0, "set int 3");

        SET_ALL_INT(set2, node)
            if (node == 5) SET_REMOVE_ITEM;
        SET_END
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{27}") == 0, "set int 5");

        set_add(set2, i2ptr(5));
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{5,27}") == 0, "set int 6");

        SET_ALL_INT(set2, node)
            if (node == 5) { SET_REMOVE_ITEM; SET_EXIT; }
        SET_END
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        sz = 0; t_assert(strcmp(buf, "{27}") == 0, "set int 8");

        SET_ALL_INT(set2, node)
            if (node == 27) { SET_REMOVE_ITEM; SET_EXIT; }
        SET_END
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(strcmp(buf, "{}") == 0 && set_size(set2) == 0, "set int 10");

        set_add(set2, 0);
        set_add(set2, i2ptr(5)); set_add(set2, i2ptr(16));
        set_add(set2, i2ptr(27));
        set_add(set2, i2ptr(6)); set_add(set2, i2ptr(17));

        sz = 0; sz = log_hash_print(buf, sz, set2, true); buf[sz++] = 0;
        printf("  set: \n%s", buf);

        i = 0;
        SET_ALL_INT(set2, node)
            node++; /* make no warning */
            if (i >= 2 && i <= 4) SET_REMOVE_ITEM;
            i++;
        SET_END

        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(
        strcmp(buf, "{0,27,6}") == 0 && set_size(set2) == 3, "set int 11");

        SET_ALL_INT(set2, node)
            node++; /* make no warning */
            SET_REMOVE_ITEM;
        SET_END
        sz = 0; sz = log_hash_print(buf, sz, set2, false); buf[sz++] = 0;
        t_assert(
        strcmp(buf, "{}") == 0 && set_size(set2) == 0, "set int 12");

        free(app2);
        set_free(&set1);
        set_free(set2);
        set_free(gv);
        printf("- set, int and string\n");
    }
    { /* check for hash code collision */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        map_t* map1 = map_init(NULL, KEY_ID(ENT_TST_INT32), 11, gv);
        map_add(map1, i2ptr(205), i2ptr(205));
        map_add(map1, i2ptr(5), i2ptr(105));
        map_add(map1, i2ptr(16), i2ptr(116));
        map_add(map1, i2ptr(206), i2ptr(206));

        int sz = 0; sz = log_hash_print(buf, sz, map1, true); buf[sz++] = 0;
        printf("%s", buf);

        t_assert(ptr2i(map_get(map1, i2ptr(205))) == 205 &&
            ptr2i(map_get(map1, i2ptr(16))) == 116 &&
            ptr2i(map_get(map1, i2ptr(5))) == 105, "hash, tst int32 1");

        int i;
        for (i = 0;i < 1000;i++)
            map_add(map1, i2ptr(i), i2ptr((1000 + i)));

        printf("  map len = %d size = %d\n", map1->len, map_size(map1));
        t_assert(map_size(map1) == 1000, "hash, tst int32 2");

        for (i = 0;i < 1000;i++)
            t_assert1(ptr2i(map_get(map1, i2ptr(i))) == 1000 + i,
                      "hash, tst int32 3");

        for (i = 0;i < 1000;i++)
            t_assert1(ptr2i(map_del(map1, i2ptr(i))) == 1000 + i,
                      "hash, tst int32 4");

        printf("  map len = %d size = %d\n", map1->len, map_size(map1));
        t_assert(map_size(map1) == 0, "hash, tst int32 5");

        set_free(map1);
        set_free(gv);
        printf("- hash, code collision\n");
    }
    { /* check large set */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        char* buf = malloc(20 * 100000);
        int i;
        for (i = 0;i < 100000;i++)
            gen_str(buf + i * 20, 19);

        set_t* set = set_init(NULL, KEY_ID(ENT_STR), 0, gv);
        printf("  gen set of strings\n");
        for (i = 0;i < 100000;i++) set_add(set, buf + i * 20);
        printf("  add set of strings done\n");

        t_assert(set_size(set) == 100000, "large set size");
        printf("  set len = %d size = %d\n", set->len, set_size(set));

        for (i = 0;i < 100000;i++)
            t_assert1(set_get(set, buf + i * 20) == buf + i * 20,
            "large set");

        for (i = 0;i < 100000;i++) set_del(set, buf + i * 20);
        t_assert(set_size(set) == 0, "large set size 1");

        free(buf);
        set_free(set);
        set_free(gv);
        printf("- set, str, large collection\n");
    }
}

static void
test_tables(void)
{
    char buf[1024];
    { /* check value collection */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        log_value_t* nstr = log_value_init("", 0, gv);
        log_value_t* nhello = log_value_init("hello", 0, gv);
        char world[7] = "worlda";
        log_value_t* nworld = log_value_init(world, 5, gv);

        char world1[5] = { 'a', 'b', 0, 'c', 'd' };
        log_value_t* nabcd = log_value_init(world1, 5, gv);


        char hello1[5] = { 'h', 'e', 'l', 'l', 'o' };
        log_value_t* nhello1 = log_value_init(hello1, 5, gv);
        log_value_t* nab = log_value_init("ab", 0, gv);

        char world2[5] = { 'a', 'b', 0, 'c', 'd' };
        log_value_t* nabcd2 = log_value_init(world2, 5, gv);

        log_value_ref(nstr);
        t_assert(set_size(gv) == 5, "value set 1");

        t_assert(nhello == nhello1 && nabcd == nabcd2 &&
            nabcd != nab && strcmp(nworld->value.a, "world") == 0,
            "value set 2");

        t_assert(nhello->ref_no == 2 && nabcd->ref_no == 2 &&
            nab->ref_no == 1 && nworld->ref_no == 1 && nstr->ref_no == 2,
            "value set 3");

        log_value_free(nhello, gv);
        log_value_free(nhello, gv);
        log_value_free(nabcd, gv);

        int sz = 0; sz = log_hash_print(buf, sz, gv, true); buf[sz++] = 0;
        printf("%s", buf);

        t_assert(set_size(gv) == 4 &&
            set_has(gv, nabcd), "value set 4");

        set_free(gv);
        printf("- value, ref_no\n");
    }
    { /* check tuple */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        log_tuple_t* tuple1 = log_tuple_init_str("2:f0:f1:f2", ':', gv);
        log_tuple_t* tuple2 = log_tuple_init_str("10:f2:f0:f3:f1", ':', gv);

        int32_t sz = 0;
        sz = log_tuple_print(buf, sz, tuple1);
        buf[sz++] = '|';
        sz = log_tuple_print(buf, sz, tuple2);
        buf[sz++] = 0;
        printf("  tuple %s %d\n", buf, sz);
        t_assert(strcmp("2:f0:f1:f2|10:f2:f0:f3:f1", buf) == 0 && sz == 26,
            "tuple str init");

        sz = 0; sz = log_hash_print(buf, sz, gv, true); buf[sz++] = 0;
        printf("%s", buf);

        log_value_t* v_f2 = log_value_init("f2", 0, gv);
        t_assert(v_f2->ref_no == 3, "tuple ref");
        log_tuple_free(tuple1, gv, true);
        log_tuple_free(tuple2, gv, true);

        sz = 0; sz = log_hash_print(buf, sz, gv, true); buf[sz++] = 0;
        printf("%s", buf);

        t_assert(v_f2->ref_no == 1 && set_size(gv) == 1,
            "tuple ref 1");

        set_free(gv);
        printf("- tuple\n");
    }
    { /* check table operation */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        array_t* key0 = log_array_init(NULL, 0, 0, gv);
        array_t* key01 = log_array_init(NULL, 0, 0, gv);
        array_add(key0, 0);
        array_add(key01, 0); array_add(key01, i2ptr(2));

        log_int_tuple_t* ikey0 = log_int_tuple_init(key0);
        log_int_tuple_t* ikey01 = log_int_tuple_init(key01);
        log_array_free(key0);
        log_array_free(key01);

        log_value_t* val_a = log_value_init("a", 0, gv);
        log_table_t* tbl = log_table_init(NULL, 1, 3, 0, gv);

        log_tuple_t* tkab = log_tuple_init_str("0:a", ':', gv);
        log_tuple_t* tkab2 = log_tuple_init_str("0:a:b", ':', gv);

        log_tuple_t* tuple1 = log_tuple_init_str("1:a:c:b", ':', gv);
        log_tuple_t* tuple2 = log_tuple_init_str("2:a:e:b", ':', gv);
        log_tuple_t* tuple21 = log_tuple_init_str("2:a:e:b", ':', gv);
        log_tuple_t* tuple3 = log_tuple_init_str("3:a:f:d", ':', gv);
        log_tuple_t* tuple4 = log_tuple_init_str("4:b:g:d", ':', gv);

        /* create index later */
        log_table_add(tbl, tuple1); log_table_add(tbl, tuple2);
        log_table_add(tbl, tuple3); log_table_add(tbl, tuple4);
        log_table_remove(tbl, tuple2);

        t_assert(val_a->ref_no == 6, "table index c0");

        int sz = 0;
        SET_ALL(&tbl->tuples, tuple, log_tuple_t*)
            sz = log_tuple_print(buf, sz, tuple);
            buf[sz++] = '|';
        SET_END
        buf[sz++] = 0;
        printf("  table tuples: %s\n", buf);
        t_assert(strcmp(buf, "4:b:g:d|1:a:c:b|3:a:f:d|") == 0,
            "table index 0");

        log_table_add(tbl, tuple21);
        int32_t i0 = log_table_add_index(tbl, ikey0);
        log_tuple_t* set = log_index_get_index(tbl, tkab, i0);

        sz = 0;
        INDEX_ALL(set, i0, t)
            sz = log_tuple_print(buf, sz, t);
            buf[sz++] = '|';
        INDEX_END
        buf[sz++] = 0;

        printf("  search table on index0 (a): %s\n", buf);
        t_assert(strcmp(buf, "2:a:e:b|3:a:f:d|1:a:c:b|") == 0,
                 "table index 1");

        int32_t i01 = log_table_add_index(tbl, ikey01);
        log_int_tuple_free(ikey0);
        log_int_tuple_free(ikey01);

        set = log_index_get_index(tbl, tkab2, i01);
        sz = 0; sz = log_index_print(buf, sz, tbl); buf[sz++] = 0;
        printf("%s", buf);

        sz = 0;
        INDEX_ALL(set, i01, t)
            sz = log_tuple_print(buf, sz, t);
            buf[sz++] = '|';
        INDEX_END
        buf[sz++] = 0;
        printf("  search table on index02 (a, b): %s\n", buf);
        t_assert(strcmp(buf, "2:a:e:b|1:a:c:b|") == 0, "table index 2");

        printf("  add tuple when index is defined\n");
        log_tuple_t* tuple5 = log_tuple_init_str("5:c:f:d", ':', gv);
        log_tuple_t* tuple6 = log_tuple_init_str("6:b:h:d", ':', gv);
        log_tuple_t* tuple7 = log_tuple_init_str("7:a:s:b", ':', gv);
        log_table_add(tbl, tuple5); log_table_add(tbl, tuple6);
        log_table_add(tbl, tuple7);

        sz = 0; sz = log_index_print(buf, sz, tbl); buf[sz++] = 0;
        printf("%s", buf);

        printf("  del tuple when index is defined\n");
        log_table_remove(tbl, tuple1);
        log_table_remove(tbl, tuple21);
        log_table_remove(tbl, tuple7);
        t_assert(val_a->ref_no == 4, "table index c1");

        sz = 0; sz = log_index_print(buf, sz, tbl); buf[sz++] = 0;
        printf("%s", buf);

        sz = 0;
        SET_ALL(&tbl->tuples, tuple, log_tuple_t*)
            sz = log_tuple_print(buf, sz, tuple);
            buf[sz++] = '|';
        SET_END
        buf[sz++] = 0;
        printf("  table tuples: %s\n", buf);
        t_assert(strcmp(buf, "4:b:g:d|6:b:h:d|3:a:f:d|5:c:f:d|") == 0,
                "table index 3");

        log_table_free(tbl);
        log_tuple_free(tkab, gv, true);
        log_tuple_free(tkab2, gv, true);
        log_value_free(val_a, gv);

        t_assert(set_size(gv) == 0, "table values released");
        set_free(gv);
        printf("- tables and tuples\n");
    }
}

static void
test_sort(void)
{
    char buf[1024];

    set_t* gv = set_init(NULL, 0, 0, NULL);
    log_set_global_value(gv);

    map_t right1, right2, rules;
    set_init(&right1, KEY_ID(ENT_VALUE), 0, gv);
    set_init(&right2, KEY_ID(ENT_VALUE), 0, gv);
    map_init(&rules, KEY_ID(ENT_VALUE) | VALUE_ID(ENT_SET), 0, gv);

    set_add(&right1, log_value_init("1", 0, gv));
    set_add(&right2, log_value_init("1", 0, gv));
    set_add(&right2, log_value_init("2", 0, gv));

    map_add(&rules, log_value_init("2", 0, gv), &right1);
    map_add(&rules, log_value_init("3", 0, gv), &right2);

    int sz = 0; sz = log_hash_print(buf, sz, &rules, false); buf[sz++] = 0;
    printf("  G=%s\n", buf);

    array_t order;
    map_t in_nodes, out_nodes;
    log_topo_sort(&rules, &order, &in_nodes, &out_nodes);

    sz = 0;
    sz = log_coll_print(buf, sz, &order, ENT_ARRAY, false);
    sz = log_coll_print(buf, sz, &in_nodes, ENT_SET, false);
    sz = log_coll_print(buf, sz, &out_nodes, ENT_SET, false);
    buf[sz++] = 0;

    t_assert(strcmp(buf, "[1,2,3]{1}{3}") == 0, "topo sort 1");
    log_array_free(&order);
    set_free(&in_nodes);
    set_free(&out_nodes);

    array_t ary1, ary2, ary3;
    log_array_init(&ary1, KEY_ID(ENT_INT32), 0, NULL);
    log_array_init(&ary2, KEY_ID(ENT_INT32), 0, NULL);
    log_array_init(&ary3, KEY_ID(ENT_INT32), 0, NULL);

    int v1[] = { 9, 7, 9, 7, 5 };
    int v2[] = { 1, 2, 3, 4, 5 };
    int v3[] = { 5, 4, 3, 2, 1 };

    int i;
    for (i = 0;i < 5;i++) {
        array_add(&ary1, i2ptr(v1[i]));
        array_add(&ary2, i2ptr(v2[i]));
        array_add(&ary3, i2ptr(v3[i]));
    }
    log_sort_array(0, &ary1, &ary2, &ary3);

    sz = 0;
    int iv1 = log_insert_item(8, &ary1, i2ptr(6), i2ptr(10), &ary2, &ary3);
    sz = log_array_print(buf, sz, &ary1, false);
    sz = log_array_print(buf, sz, &ary2, false);
    sz = log_array_print(buf, sz, &ary3, false);
    int iv2 = log_insert_item(8, &ary1, i2ptr(7), i2ptr(11), &ary2, &ary3);
    sz = log_array_print(buf, sz, &ary1, false);
    sz = log_array_print(buf, sz, &ary2, false);
    sz = log_array_print(buf, sz, &ary3, false);
    buf[sz++] = 0;
    printf("  sort: %s\n", buf);

    t_assert(iv1 == 3 && iv2 == 4 && strcmp(buf,
    "[5,7,7,8,9,9][5,2,4,6,1,3][1,4,2,10,5,3]"
    "[5,7,7,8,8,9,9][5,2,4,6,7,1,3][1,4,2,10,11,5,3]") == 0, "sort insert");

    log_array_free(&ary1); log_array_free(&ary2); log_array_free(&ary3);
    set_free(gv);
    printf("- sort and insert\n");
}

static void
test_sync(void)
{
    char buf[1024];
    {
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        log_sync_init(
            "table(a,b) : x(a,'aa')\n"
            "# comment \n"
            "y(b,-, -) ; z(aparam) > y(x) \n"
            ".  # last line"
        ,gv);

        TYPE2(map_t, log_value_t*, array_t*) map;
        log_sync_parse(&map);

        int sz = 0;
        sz = log_hash_print(buf, sz, &map, false); buf[sz++] = 0;
        printf("  sync %s\n", buf);

        t_assert(0 == strcmp(buf,
        "{z->[[u,z,t,aparam],[,y,t,x]],"
        "table->[[j,table,t,a,t,b],[,x,t,a,s,aa],[,y,t,b,-,,-,]]}"),
        "sync check 1");
        map_free(&map);
        set_free(gv);
        printf("- log syntax\n");
    }
    {
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        log_sync_init(
        /*
        "Xx2(a) : x1(a,'aa'); X3(a) : x1(a, b) Xx2(b); _EXTERNAL(x1, func)."
            // input, output cannot be external
        "Xx2(a) : x1(a,'aa'); X3(a) : x1(a, b) Xx2(b); _EXTERNAL(X5, func)."
            // invalid external
        "X2(a) : X1(a,'aa'); X3(a) : X1(a, b, c) X2(b)."
            // upper / lower case wrong
        "X2(a, b) : x2(b) x1(a) x1(a) x1(a)." 	// join more than twice
        "X2(a) > x1(a) x1(a) x1(a)." 	// union more than twice
        "X2(a, b) > x1(a) x1(a, b)." 	// table size mismatch
        "X2(a, b) : x1(a) x2(a, b); X3(v) : x2(z)." 	// table size mismatch
        "X2(a, 'aa') > x1(a)." 	// constant not allowed in left
        "X2(a, -) : x1(a)." 	// ignored not allowed in left
        "X2(a, b) > x1(a, c)." 	// union param not found
        "X2(a) : x1(a, c)." 	// param not used should be 'ignored'
        "X2(a, z) : x1(a, -)." 	// param not defined
         */
        "Xx2(a) : x1(a,'aa', -); X3(a) : Xx2(a) x1(a, -, b) Xx2(b)."// correct
        /*
        " Span(ls_id, host_id) : ls(ls_id, vif) vif_place(host_id, vif); \n"
        " HOST_LS(host1, ls, host2) : Span(ls, host1) Span(ls, host2). "
         */
        , gv);

        TYPE2(map_t, log_value_t*, array_t*) map;
        log_sync_parse(&map);

        int sz;
        sz = 0; sz = log_hash_print(buf, sz, &map, false); buf[sz++] = 0;
        printf("  sync %s\n", buf);

        log_rule_set_t rs;
        log_rule_set_init(&rs, gv);
        log_sem_process(&rs, &map);
        sz = 0; sz = log_rule_set_print(buf, sz, &rs); buf[sz++] = 0;
        printf("  sem=\n%s\n", buf);

        log_rule_set_free(&rs);
        map_free(&map);
        set_free(gv);
        printf("- log semantics\n");
    }
}

static void
test_join(void)
{
    char buf[1024];
    {
        /* do join table 2 */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        log_table_t* tbl1 = log_table_init(NULL, 0, 3, 0, gv);
        log_table_t* tbl2 = log_table_init(NULL, 1, 4, 0, gv);

        log_table_add(tbl1, log_tuple_init_str("2 :1:2:7", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1 :1:3:8", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1 :1:5:9", ':', gv));

        log_table_add(tbl2, log_tuple_init_str("1 :3:1:2:0", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1 :4:1:2:0", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("9 :4:1:5:0", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1 :4:1:5:1", ':', gv));

        TYPE(array_t*, int32_t) ints =
                log_array_init(NULL, KEY_ID(ENT_INT32), 0, gv);
        array_add(ints, i2ptr(1));
        array_add(ints, i2ptr(2)); array_add(ints, i2ptr(3));
        log_int_tuple_t* key0 = log_int_tuple_init(ints);
        log_array_free(ints);

        log_join_param_t jps;
        log_join_param_t* jp = log_join_param_init(&jps, key0, gv);

        array_add(&jp->select1i, 0);
        array_add(&jp->select1i, i2ptr(1));
        array_add(&jp->select1i, 0);
        array_add(&jp->select1, NULL);
        array_add(&jp->select1, NULL); array_add(&jp->select1,
        log_value_init("0", 0, gv));

        array_add(&jp->rem1, 0);
        array_add(&jp->rem2, 0);

        log_table_t* tbl3 = log_tblopr_join(tbl1, tbl2, jp);
        log_join_param_free(jp);

        int sz = 0; sz = log_table_print(buf, sz, tbl2, true); buf[sz++] = 0;
        printf("  cond join tbl2 index=%s\n", buf);
        sz = 0; sz = log_table_print(buf, sz, tbl3, false); buf[sz++] = 0;
        printf("  cond join result=%s\n", buf);
        t_assert(0 == strcmp(buf, "{2:1:3,3:1:4}"), "cond join 1");

        log_table_free(tbl1);
        log_table_free(tbl2);
        log_table_free(tbl3);
        set_free(gv);
    }
    {
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);

        log_table_t* tbl1 = log_table_init(NULL, 0, 1, 0, gv);
        log_table_t* tbl2 = log_table_init(NULL, 1, 3, 0, gv);

        log_table_add(tbl1, log_tuple_init_str("2 :1", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1 :2", ':', gv));

        log_table_add(tbl2, log_tuple_init_str("8 :3:4:1", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1 :3:5:0", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1 :5:4:1", ':', gv));

        TYPE(array_t*, int32_t) ints = log_array_init(
                                       NULL, KEY_ID(ENT_INT32), 0, gv);
        array_add(ints, i2ptr(2));
        log_int_tuple_t* key0 = log_int_tuple_init(ints);
        log_array_free(ints);

        log_join_param_t jps;
        log_join_param_t* jp = log_join_param_init(&jps, key0, gv);

        array_add(&jp->select1i, 0);
        array_add(&jp->select1, log_value_init("1", 0, gv));

        array_add(&jp->rem1, i2ptr(0));
        array_add(&jp->rem2, i2ptr(1));

        log_table_t* tbl3 = log_tblopr_join(tbl1, tbl2, jp);
        log_join_param_free(jp);

        int sz = 0; sz = log_table_print(buf, sz, tbl2, true); buf[sz++] = 0;
        printf("  join tbl2 index=%s\n", buf);
        sz = 0; sz = log_table_print(buf, sz, tbl3, false); buf[sz++] = 0;
        printf("  full join result=%s\n", buf);
        t_assert(0 == strcmp(buf, "{2:2:4,4:1:4}"), "full join 1");

        log_table_free(tbl1);
        log_table_free(tbl2);
        log_table_free(tbl3);
        set_free(gv);
    }
    {
        /* do union */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value( gv);

        log_engine_t log;
        log_engine_init(&log, gv);

        log_sync_init("X(a0, a2, a1) : x(a2, a1, -, 'cst', a0) .", gv);
        TYPE2(map_t, log_value_t*, array_t*) map;

        log_sync_parse(&map);
        log_sem_process(&log.rule_set, &map);
        map_free(&map);

        log_table_t* tbl1 = log_table_init(NULL, 0, 5, 0, gv);
        log_table_t* tbl2 = log_table_init(NULL, 1, 3, 0, gv);

        log_table_add(tbl1, log_tuple_init_str("1:a:b:c:cst:d", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1:a:b:c:dst:d", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1:a:b:d:cst:d", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1:a:b:d:cst:e", ':', gv));

        log_eng_do_union(&log, tbl1, tbl2);

        int sz = 0; sz = log_table_print(buf, sz, tbl2, false); buf[sz++] = 0;
        printf("  union = %s\n", buf);
        t_assert(0 == strcmp(buf, "{1:e:a:b,2:d:a:b}"), "union 1");

        log_table_free(tbl1); log_table_free(tbl2);
        log_engine_free(&log);
        set_free(gv);
    }
    { /* do self join 1 */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse(
            "X(b, a, c) : x(a, b, 'v', -, c) x(b, 'w', -, a, c) .", gv);

        log_table_t* tbl0_org = map_get(&eng->tables, 0);
        log_table_add(tbl0_org, log_tuple_init_str("1:a:b:c:d:e", ':', gv));
        log_table_add(tbl0_org, log_tuple_init_str("1:a:y:v:a:e", ':', gv));

        log_table_t* tbl1 = log_table_init(NULL, 0, 5, 0, gv);
        log_table_t* tbl2 = log_table_init(NULL, 1, 3, 0, gv);
        log_table_add(tbl1, log_tuple_init_str("1:w:w:v:w:e", ':', gv));

        log_eng_do_join(eng, tbl1, tbl2);
        int sz = 0; sz = log_table_print(buf, sz, tbl2, false); buf[sz++] = 0;
        printf("  self join simple match = %s\n", buf);
        t_assert(0 == strcmp(buf, "{1:w:w:e}"), "self join 1");

        log_table_free(tbl1); log_table_free(tbl2);
        log_engine_free(eng);
        set_free(gv);
    }
    {
        // do self join 2
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse("X(a, b, c) : x(a, b) x(a, c) .", gv);

        log_table_t* tbl0_o = map_get(&eng->tables, 0);
        log_table_t* tbl0 = log_table_init(NULL, 0, 2, 0, gv);
        log_table_t* tbl2 = log_table_init(NULL, 1, 3, 0, gv);
        log_table_add(tbl0, log_tuple_init_str("1:1:1", ':', gv));
        log_table_add(tbl0, log_tuple_init_str("1:1:2", ':', gv));
        log_table_add(tbl0, log_tuple_init_str("1:2:1", ':', gv));

        log_eng_do_join(eng, tbl0, tbl2);

        int sz = 0; sz = log_table_print(buf, sz, tbl2, false); buf[sz++] = 0;
        printf("  self join simple initial = %s\n", buf);
        t_assert(0 == strcmp(buf,
            "{1:2:1:1,1:1:1:2,1:1:1:1,1:1:2:2,1:1:2:1}"),
            "self join simple init 1");

        log_table_add(tbl0_o, log_tuple_init_str("1:1:1", ':', gv));
        log_table_add(tbl0_o, log_tuple_init_str("1:1:2", ':', gv));
        log_table_add(tbl0_o, log_tuple_init_str("1:2:1", ':', gv));

        log_table_t* tbl_0 = log_table_init(NULL, 0, 2, 0, gv);
        log_table_t* tbl_2 = log_table_init(NULL, 1, 3, 0, gv);
        log_table_add(tbl_0, log_tuple_init_str("1:1:3", ':', gv));

        log_eng_do_join(eng, tbl_0, tbl_2);
        sz = 0; sz = log_table_print(buf, sz, tbl_2, false); buf[sz++] = 0;
        printf("  self join simple delta = %s\n", buf);
        t_assert(0 == strcmp(buf,
            "{1:1:1:3,1:1:3:2,1:1:3:3,1:1:2:3,1:1:3:1}"),
            "self join simple delta 1");

        log_table_free(tbl_0); log_table_free(tbl_2);
        log_table_free(tbl0); log_table_free(tbl2);
        log_engine_free(eng);
        set_free(gv);
    }
    {
        // do join 3
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse(
            "R(h, b, c, d) : h(h, p1, p2) p1(p1, -, b) p2(p2, d, c) .",gv);

        log_table_t* tbl0_h = map_get(&eng->tables, i2ptr(0));
        log_table_t* tbl0_p1 = map_get(&eng->tables, i2ptr(1));
        log_table_t* tbl0_p2 = map_get(&eng->tables, i2ptr(2));

        log_table_add(tbl0_h, log_tuple_init_str("1:h1:px:py", ':', gv));
        log_table_add(tbl0_p1, log_tuple_init_str("1:p1:a1:b", ':', gv));
        log_table_add(tbl0_p1, log_tuple_init_str("1:p1:a2:b", ':', gv));
        log_table_add(tbl0_p2, log_tuple_init_str("1:p2:c:d", ':', gv));

        log_table_t* tbl1 = log_table_init(NULL, 0, 3, 0, gv);
        log_table_t* tbl2 = log_table_init(NULL, 3, 4, 0, gv);
        log_table_add(tbl1, log_tuple_init_str("1:h1:p1:p2", ':', gv));

        log_eng_do_join(eng, tbl1, tbl2);
        int sz = 0; sz = log_table_print(buf, sz, tbl2, false); buf[sz++] = 0;
        printf("  join 3 simple = %s\n", buf);
        t_assert(0 == strcmp(buf, "{2:h1:b:d:c}"),
            "join 3 simple");

        log_table_free(tbl1); log_table_free(tbl2);
        log_engine_free(eng);
        set_free(gv);
    }
    printf("- join and union\n");
}

static bool
test_ext_func(log_engine_t* eng, log_table_t* inp, log_table_t* del_out,
              log_table_t* add_out)
{
    char buf[256];

    if (inp == NULL) return true; /* reset state */
    log_value_t* tn = map_get(
        &eng->rule_set.rule_name_map, i2ptr(del_out->table_index));
    if (strcmp(tn->value.a, "Mm2") != 0) return false;

    int sz = 0; sz = log_table_print(buf, sz, inp, false); buf[sz] = 0;
    printf("  run ext inp = %s\n", buf);

    log_table_t* output = inp->is_remove ? del_out : add_out;
    log_value_t* tv[1];

    SET_ALL(&inp->tuples, tuple, log_tuple_t*)
        int sz = sprintf(buf, "aa%scc", tuple->values[0]->value.a);
        log_value_t* nv = log_value_init(buf, sz, inp->m.glb_values);
        tv[0] = nv;

        log_tuple_t* nt = log_tuple_init_val(tv, 1);
        log_table_add(output, nt);
    SET_END

    sz = 0; sz = log_table_print(buf, sz, output, false); buf[sz] = 0;
    printf("  run ext inp remove = %s\n", inp->is_remove ? "true" : "false");
    printf("  run ext out = %s\n", buf);
    return true;
}

static void
test_delta(void)
{
    char buf[1024];
    {
        /* delta with external function */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse("M(a) : inp(a) Mm2(a); Mm2(a) : i(a) .", gv);
        /* {0=inp, 1=i, 2=Mm2, 3=M} */

        log_eng_set_ext_func(eng, test_ext_func);
        log_table_t* tbl1 = map_get(&eng->tables, 0);
        log_table_t* tbl2 = log_table_init(NULL, 1, 1, 0, gv);

        log_table_add(tbl1, log_tuple_init_str("1:aaVbbcc", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1:bb", ':', gv));

        TYPE(array_t*, log_table_t*) inp_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        array_add(inp_insert, tbl2);

        array_t* res = log_eng_delta(eng, inp_remove, inp_insert);
        int sz = 0; sz = log_array_print(buf, sz, res, false); buf[sz] = 0;
        printf("  delta ext empty=%s\n", buf);
        t_assert(array_size(res) == 0, "delta ext func 0");

        log_array_free(res);
        log_array_free(inp_remove);	log_array_free(inp_insert);
        log_engine_free(eng); set_free(gv);
    }
    {
        /* delta with external function */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse("M(a) : inp(a) Mm2(a); Mm2(a) : i(a) .", gv);
        /* {0=inp, 1=i, 2=Mm2, 3=M} */

        log_eng_set_ext_func(eng, test_ext_func);
        log_table_t* tbl1 = map_get(&eng->tables, 0);
        log_table_t* tbl2 = log_table_init(NULL, 1, 1, 0, gv);

        log_table_add(tbl1, log_tuple_init_str("1:aabbcc", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1:bb", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1:ee", ':', gv));

        TYPE(array_t*, log_table_t*) inp_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        array_add(inp_insert, tbl2);

        array_t* res = log_eng_delta(eng, inp_remove, inp_insert);
        int sz = 0; sz = log_array_print(buf, sz, res, false); buf[sz] = 0;
        printf("  delta ext=%s\n", buf);
        t_assert(0 == strcmp(buf, "[{1:aabbcc}]"), "delta ext 1");

        sz = 0;
        sz = log_hash_print(buf, sz, &eng->tables, false); buf[sz] = 0;
        printf("  all tables=%s\n", buf);

        log_table_t* tbl2d = log_table_init(NULL, 1, 1, 0, gv);
        tbl2d->is_remove = true;
        log_table_add(tbl2d, log_tuple_init_str("1:bb", ':', gv));

        TYPE(array_t*, log_table_t*) inp1_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp1_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        array_add(inp1_remove, tbl2d);

        array_t* res1 = log_eng_delta(eng, inp1_remove, inp1_insert);
        sz = 0; sz = log_array_print(buf, sz, res1, false); buf[sz] = 0;
        printf("  delta ext rmv=%s\n", buf);
        t_assert(0 == strcmp(buf, "[{1:aabbcc}]") &&
            ((log_table_t*)array_get(res1, 0))->is_remove == true,
            "delta ext rmv 1");

        sz = 0;
        sz = log_hash_print(buf, sz, &eng->tables, false); buf[sz] = 0;

        log_array_free(res); log_array_free(inp_remove);
        log_array_free(inp_insert);
        log_array_free(res1); log_array_free(inp1_remove);
        log_array_free(inp1_insert);

        log_engine_free(eng); set_free(gv);
        printf("  all tables=%s\n", buf);
    }
    printf("- delta and ext func\n");
}

static void
test_delta_misc(void)
{
    char buf[1024];
    {
        /* input's counter should be ignored */
        int sz;
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse("Xy(a) : x(a, -); Xy1(a) : Xy(a); Y(a) : Xy1(a) .", gv);

        log_table_t* tbl1 = log_table_init(NULL, 0, 2, 0, gv); /* tbl x */
        log_table_add(tbl1, log_tuple_init_str("1:1:1", ':', gv));
        log_table_add(tbl1, log_tuple_init_str("1:1:2", ':', gv));

        TYPE(array_t*, log_table_t*) inp_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        array_add(inp_insert, tbl1);

        array_t* res = log_eng_delta(eng, inp_remove, inp_insert);
        sz = 0;
        sz = log_hash_print(buf, sz, &eng->tables, false); buf[sz] = 0;

        printf("  delta, counter %s\n", buf);
        t_assert(0 == strcmp(buf, "{0->{1:1:1,1:1:2},1->{2:1},2->{1:1}}"),
            "delta, counter value 1");

        log_array_free(res); log_array_free(inp_remove);
        log_array_free(inp_insert);

        log_table_t* tbl2 = log_table_init(NULL, 0, 2, 0, gv); /* tbl x */
        tbl2->is_remove = true;
        log_table_add(tbl2, log_tuple_init_str("1:1:1", ':', gv));
        log_table_add(tbl2, log_tuple_init_str("1:1:2", ':', gv));

        TYPE(array_t*, log_table_t*) inp1_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp1_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        array_add(inp1_remove, tbl2);

        array_t* res1 = log_eng_delta(eng, inp1_remove, inp1_insert);
        /* no assert issue when minus */
        sz = 0; sz = log_array_print(buf, sz, res1, false); buf[sz] = 0;

        t_assert(0 == strcmp(buf, "[{1:1}]"), "delta, counter value 2");
        printf("  delta, counter minus%s\n", buf);

        log_array_free(res1); log_array_free(inp1_remove);
        log_array_free(inp1_insert);
        log_engine_free(eng); set_free(gv);
    }
    {
        /* merge add and remove for normal join */
        set_t* gv = set_init(NULL, 0, 0, NULL);
        log_set_global_value(gv);
        log_engine_t* eng =
        log_eng_parse("A(a) : b(a, b) c(b) .", gv);

        log_table_t* tbl1 = log_table_init(NULL, 1, 1, 0, gv); /* tbl c */
        log_table_add(tbl1, log_tuple_init_str("1:1", ':', gv));

        TYPE(array_t*, log_table_t*) inp_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        array_add(inp_insert, tbl1);
        array_t* res = log_eng_delta(eng, inp_remove, inp_insert);

        /* when testing, should reorder the 2 doJoin in delta() */
        log_table_t* tbl2 = log_table_init(NULL, 1, 1, 0, gv); /* tbl c */
        log_table_t* tbl3 = log_table_init(NULL, 0, 2, 0, gv); /* tbl b */

        tbl2->is_remove = true;
        log_table_add(tbl2, log_tuple_init_str("1:1", ':', gv));
        log_table_add(tbl3, log_tuple_init_str("1:2:1", ':', gv));

        TYPE(array_t*, log_table_t*) inp1_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp1_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);

        array_add(inp1_remove, tbl2);
        array_add(inp1_insert, tbl3);
        array_t* res1 = log_eng_delta(eng, inp1_remove, inp1_insert);

        int sz = 0; sz = log_hash_print(buf, sz, &eng->tables, false);
        buf[sz] = 0;
        printf("  merge add and remove %s\n", buf);
        t_assert(array_size(res1) == 0, "merge add and remove");

        log_array_free(res); log_array_free(inp_remove);
        log_array_free(inp_insert);
        log_array_free(res1); log_array_free(inp1_remove);
        log_array_free(inp1_insert);
        log_engine_free(eng); set_free(gv);
    }
    printf("- delta, misc\n");
}

static void
test_delta_more(void)
{

    const char* rules =

"LS_host_set(ls_id, host_id) : logical_switch(ls_id, port_id) "
"port_bind(port_id, vif_id) dest_place(host_id, vif_id); "
"LS_HOST_SET(host_id, ls_id, host_id_item) : LS_host_set(ls_id, host_id) "
"LS_host_set(ls_id, host_id_item); "
"LS_HOST_TUNNEL(host_id, host_id_item, tunnel_ip) : "
"LS_host_set(ls_id, host_id) "
"LS_host_set(ls_id, host_id_item) dest_tunnel(host_id_item,tunnel_ip) . ";

    const char* d1[] = {
        "+:1:logical_switch", "1:ls1:lp1",
        "+:1:port_bind", "1:lp1:vif1",
        "+:1:dest_place", "1:h1:vif1",
        "+:1:dest_tunnel", "1:h1:ip1"
    };

    const char* d2[] = {
        "+:1:port_bind", "1:lp2:vif2",
        "+:1:dest_place", "1:h2:vif2",
        "+:1:logical_switch", "1:ls1:lp2",
        "+:1:dest_tunnel", "1:h2:ip2"
    };

    const char* d3[] = {
        "-:1:dest_place", "1:h2:vif2",
    };

    const char* d4[] = {
        "-:1:logical_switch", "1:ls1:lp1",
    };

    const char* d5[] = {
        "-:1:logical_switch", "1:ls1:lp2",
        "+:2:port_bind", "1:lp1:vif1", "1:lp2:vif2",
        "+:1:dest_place", "1:h1:vif1",
        "+:2:dest_tunnel", "1:h1:ip1", "1:h2:ip2"
    };

    char buf[1024];
    set_t* gv = set_init(NULL, 0, 0, NULL);
    log_set_global_value(gv);
    log_engine_t* eng =	log_eng_parse(rules, gv);

    TYPE(array_t*, log_table_t*) inp_remove =
            log_array_init(NULL, ENT_TABLE, 0, gv);
    TYPE(array_t*, log_table_t*) inp_insert =
            log_array_init(NULL, ENT_TABLE, 0, gv);
    log_io_parse_line(NULL, NULL, false, NULL, NULL);

    int i;
    for (i = 0;i < sizeof d1 / sizeof(char*);i++)
    t_assert1(log_io_parse_line(d1[i], eng, false, inp_remove, inp_insert),
            "delta more 0");

    array_t* res = log_eng_delta(eng, inp_remove, inp_insert);
    int sz = 0; sz = log_io_gen_line(buf, sz, eng, res); buf[sz] = 0;

    t_assert(0 == strcmp(buf,
        "+:1:LS_HOST_TUNNEL\n1:h1:h1:ip1\n+:1:LS_HOST_SET\n1:h1:ls1:h1\n"),
        "delta more 1");

    log_array_free(inp_remove); log_array_free(inp_insert);
    log_array_free(res);

    inp_remove = log_array_init(NULL, ENT_TABLE, 0, gv);
    inp_insert = log_array_init(NULL, ENT_TABLE, 0, gv);
    log_io_parse_line(NULL, NULL, false, NULL, NULL);

    for (i = 0;i < sizeof d2 / sizeof(char*);i++)
    t_assert1(log_io_parse_line(d2[i], eng, false, inp_remove, inp_insert),
        "delta more 2");

    res = log_eng_delta(eng, inp_remove, inp_insert);
    sz = 0; sz = log_io_gen_line(buf, sz, eng, res); buf[sz] = 0;

    t_assert(0 == strcmp(buf,
    "+:3:LS_HOST_TUNNEL\n1:h2:h1:ip1\n1:h1:h2:ip2\n1:h2:h2:ip2\n"
    "+:3:LS_HOST_SET\n1:h2:ls1:h2\n1:h1:ls1:h2\n1:h2:ls1:h1\n"),
    "delta more 3");

    log_array_free(inp_remove); log_array_free(inp_insert);
    log_array_free(res);

    inp_remove = log_array_init(NULL, ENT_TABLE, 0, gv);
    inp_insert = log_array_init(NULL, ENT_TABLE, 0, gv);
    log_io_parse_line(NULL, NULL, false, NULL, NULL);

    for (i = 0;i < sizeof d3 / sizeof(char*);i++)
    t_assert1(log_io_parse_line(d3[i], eng, false, inp_remove, inp_insert),
        "delta more 4");

    res = log_eng_delta(eng, inp_remove, inp_insert);
    sz = 0; sz = log_io_gen_line(buf, sz, eng, res); buf[sz] = 0;

    t_assert(0 == strcmp(buf,
    "-:3:LS_HOST_TUNNEL\n1:h2:h1:ip1\n1:h1:h2:ip2\n1:h2:h2:ip2\n"
    "-:3:LS_HOST_SET\n1:h2:ls1:h2\n1:h1:ls1:h2\n1:h2:ls1:h1\n"
    ), "delta more 5");

    log_array_free(inp_remove); log_array_free(inp_insert);
    log_array_free(res);

    inp_remove = log_array_init(NULL, ENT_TABLE, 0, gv);
    inp_insert = log_array_init(NULL, ENT_TABLE, 0, gv);
    log_io_parse_line(NULL, NULL, false, NULL, NULL);

    for (i = 0;i < sizeof d4 / sizeof(char*);i++)
    t_assert1(log_io_parse_line(d4[i], eng, false, inp_remove, inp_insert),
        "delta more 5");

    res = log_eng_delta(eng, inp_remove, inp_insert);
    sz = 0; sz = log_io_gen_line(buf, sz, eng, res); buf[sz] = 0;

    t_assert(0 == strcmp(buf,
    "-:1:LS_HOST_TUNNEL\n1:h1:h1:ip1\n-:1:LS_HOST_SET\n1:h1:ls1:h1\n"
    ), "delta more 6");

    log_array_free(inp_remove); log_array_free(inp_insert);
    log_array_free(res);

    inp_remove = log_array_init(NULL, ENT_TABLE, 0, gv);
    inp_insert = log_array_init(NULL, ENT_TABLE, 0, gv);
    log_io_parse_line(NULL, NULL, false, NULL, NULL);

    for (i = 0;i < sizeof d5 / sizeof(char*);i++)
    t_assert1(log_io_parse_line(d5[i], eng, false, inp_remove, inp_insert),
        "delta more 6");

    res = log_eng_delta(eng, inp_remove, inp_insert);
    sz = 0; sz = log_io_gen_line(buf, sz, eng, res); buf[sz] = 0;

    t_assert(0 == strcmp(buf,""), "delta more 7");
    log_array_free(inp_remove); log_array_free(inp_insert);
    log_array_free(res);

    log_engine_free(eng);
    set_free(gv);
    printf("- delta, more\n");
}

static int64_t
calc_tm(struct timespec* ts0, struct timespec* ts1)
{
    int64_t t0 = ts0->tv_sec * 1000 * 1000L + ts0->tv_nsec / 1000;
    int64_t t1 = ts1->tv_sec * 1000 * 1000L + ts1->tv_nsec / 1000;
    return t1 - t0;
}

static void
test_join_perf(int32_t sz1, int32_t sz2)
{
    /* correct value for full join is sz1 * sz2 * sz2
     * correct value for delta join is sz2 * 2 + 1
     */

    struct timespec ts0, ts1;

    set_t* gv = set_init(NULL, 0, 0, NULL);
    log_set_global_value(gv);
    log_engine_t* eng =	log_eng_parse(
        "TABLE(b, a, c) : table1(a, b) table1(a, c).", gv);

    TYPE(array_t*, log_table_t*) inp_remove =
            log_array_init(NULL, ENT_TABLE, 0, gv);
    TYPE(array_t*, log_table_t*) inp_insert =
            log_array_init(NULL, ENT_TABLE, 0, gv);

    int i, j;
    char buf[1024];

    log_table_t* tbl1 = log_table_init(NULL, 0, 2, 0, gv);
    for (i = 0;i < sz1;i++)
        for (j = 0;j < sz2;j++) {
            sprintf(buf, "1:ID_%d:XY_%d", i, j);
            log_tuple_t* tuple = log_tuple_init_str(buf, ':', gv);
            log_table_add(tbl1, tuple);
        }

    array_add(inp_insert, tbl1);

    clock_gettime(CLOCK_MONOTONIC, &ts0);
    array_t* res = log_eng_delta(eng, inp_remove, inp_insert);
    clock_gettime(CLOCK_MONOTONIC, &ts1);
    log_table_t* res_tbl = array_get(res, 0);

    printf("  join sz1=%d sz2=%d\n", sz1, sz2);
    printf("  full run = %d buckets = %d\n",
        table_size(res_tbl), res_tbl->tuples.len);

    printf("  time = %" PRId64 " us\n", calc_tm(&ts0, &ts1));
    log_array_free(inp_remove);
    log_array_free(inp_insert);
    log_array_free(res);

    inp_remove = log_array_init(NULL, ENT_TABLE, 0, gv);
    inp_insert = log_array_init(NULL, ENT_TABLE, 0, gv);

    tbl1 = log_table_init(NULL, 0, 2, 0, gv);
    log_table_add(tbl1, log_tuple_init_str("1:ID_0:XY_new_item", ':', gv));
    array_add(inp_insert, tbl1);

    clock_gettime(CLOCK_MONOTONIC, &ts0);
    res = log_eng_delta(eng, inp_remove, inp_insert);
    clock_gettime(CLOCK_MONOTONIC, &ts1);

    res_tbl = array_get(res, 0);
    printf("  delta run = %d\n", table_size(res_tbl));
    printf("  time = %" PRId64 " us\n", calc_tm(&ts0, &ts1));
    log_array_free(inp_remove);
    log_array_free(inp_insert);
    log_array_free(res);

    log_engine_free(eng);
    set_free(gv);
    printf("- join perf\n");
}

static void
test_interactive(void)
{
    /* interactive engine for testing purpose */
    log_set_sep(':', '\n');
    printf("Input rules, e.g. R(a):r(a).\nuse EOF as end\n");
    char inp[4096];
    inp[0] = 0;

    for (;;) {
        char buf[1024];
        if (scanf("%s", buf) != 1) continue;
        if (strcmp(buf, "EOF") == 0) break;
        strcat(inp, buf);
    }

    set_t* gv = set_init(NULL, 0, 0, NULL);
    log_set_global_value(gv);
    log_engine_t* eng = log_eng_parse(inp, gv);

    for (;;) {
        TYPE(array_t*, log_table_t*) inp_remove =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        TYPE(array_t*, log_table_t*) inp_insert =
                log_array_init(NULL, ENT_TABLE, 0, gv);
        log_io_parse_line(NULL, NULL, false, NULL, NULL);

        printf("Input changes, e.g. +:1:tbl_name|1:f0:f1|.\n"
               "use +, -, ? for add, remove, or query.\n"
               "could input multiple tables. the number in table name\n"
               "line indicates number of tuples to follow.\n"
               "'|' stands for new line. use '.' to exit\n"
               "for query, field value could be empty.\n");

        bool is_query = false;
        for (;;) {
            if (scanf("%s", inp) != 1) continue;
            if (strcmp(inp, ".") == 0) break;

            if (is_query == false && strlen(inp) > 0 && inp[0] == '?') {
                inp[0] = '+';
                is_query = true;
            }

            bool res = log_io_parse_line(inp, eng,
                    is_query ? true : false, inp_remove, inp_insert);
            if (res == false) {
                printf("Error in format\n");
                break;
            }
        }

        if (array_size(inp_remove) == 0 && array_size(inp_insert) == 0) {
            log_array_free(inp_remove); log_array_free(inp_insert); break;
        }

        array_t* res = is_query ?
                log_eng_query(eng, inp_insert) :
                log_eng_delta(eng, inp_remove, inp_insert);

        int sz = 0; sz = log_io_gen_line(inp, sz, eng, res); inp[sz] = 0;
        printf("Output\n%s\n", inp);

        log_array_free(inp_remove); log_array_free(inp_insert);
        log_array_free(res);
    }

    log_engine_free(eng);
    set_free(gv);
}

static void
test_api(void)
{
    const char* p, *p1, *p2, *p3, *p4, *p5;
    int32_t sz, sz1, sz2;
    bool rmv, rmv1;

    void* eng = datalog_init("R2(a,b):r2(a,b); R1(a):r1(a).",
        /* ext func not provided */NULL);

    rmv = datalog_put_table(eng, /* adding */false, "r1");
    /* first tuple for r1 */
    datalog_put_field(eng, "r_1a", 0);

    rmv1 = datalog_put_table(eng, false, "r2");
    /* first tuple for r2 */
    datalog_put_field(eng, "r2_1a", /* c-str*/ 0);
    datalog_put_field(eng, "r2_1bx", /* len */5);
    /* second tuple r2 */
    datalog_put_field(eng, "r2_2a", 0);
    datalog_put_field(eng, "r2_2b", 0);

    datalog_opr(eng, /* delta change */false);
    t_assert(rmv && rmv1, "api 0");

    /* get output table R2 */
    rmv1 = datalog_get_table(eng, &rmv, &p, &sz, &sz1);

    t_assert(0 == strcmp(p, "R2") && sz == 2 && sz1 ==2 &&
             rmv == false && rmv1 == true, "api 1");

    /* first tuple */
    datalog_get_field(eng, &p1, &sz);
    datalog_get_field(eng, &p2, &sz1);
    /* second tuple */
    datalog_get_field(eng, &p3, &sz);
    rmv = datalog_get_field(eng, &p4, &sz);
    /* indicates reaching next table */
    rmv1 = datalog_get_field(eng, &p5, &sz);

    t_assert(0 == strcmp(p1, "r2_1a") && 0 == strcmp(p2, "r2_1b") &&
             0 == strcmp(p3, "r2_2a") && 0 == strcmp(p4, "r2_2b")
             && sz == 5 && sz1 == 5 && rmv == true
             && rmv1 == false, "api 2");

    /* get output table R1 */
    rmv1 = datalog_get_table(eng, &rmv, &p, &sz, &sz1);
    t_assert(0 == strcmp(p, "R1") && sz == 1 && sz1 == 1 &&
        rmv == false && rmv1 == true, "api 3");

    rmv = datalog_get_field(eng, &p1, &sz);
    /* indicates reaching next table */
    rmv1 = datalog_get_field(eng, &p2, &sz);

    t_assert(0 == strcmp(p1, "r_1a") &&
             sz == 4 && rmv == true && rmv1 == false, "api 4");

    /* no more table returned */
    rmv = datalog_get_table(eng, &rmv, &p, &sz, &sz1);
    t_assert(rmv == false, "api 5");

    datalog_put_table(eng, false, "r2");
    datalog_put_field(eng, "r2_1a0", 0);
    datalog_put_field(eng, "r2_1b", 0);
    datalog_opr(eng, false);
    datalog_get_table(eng, &rmv, &p, &sz, &sz1);
    /* it is ok to skip tuples of a table */
    datalog_get_table(eng, &rmv, &p, &sz, &sz1);

    datalog_put_table(eng, false, "r2");
    datalog_put_field(eng, NULL, 0);
    datalog_put_field(eng, "r2_1b", 0);
    datalog_opr(eng, /* query */true);

    rmv = datalog_get_table(eng, &rmv, &p, &sz2, &sz1);
    datalog_get_field(eng, &p1, &sz);
    datalog_get_field(eng, &p2, &sz);
    datalog_get_field(eng, &p3, &sz);
    datalog_get_field(eng, &p4, &sz);
    rmv1 = datalog_get_table(eng, &rmv, &p, &sz, &sz1);

    t_assert(0 == strcmp(p1, "r2_1a") && sz2 == 2 &&
             sz1 == 2 && rmv == true && rmv1 == false, "api 5");

    datalog_free(eng);
    printf("- api\n");
}

static void
test_datalog(int argc, char** argv)
{
    if (argc == 2 && !strcmp(argv[1], "test")) {
        log_set_sep(':', '\n');

        test_collections();
        test_tables();
        test_sort();
        test_sync();
        test_join();
        test_delta();
        test_delta_misc();
        test_delta_more();
        test_join_perf(100, 100);
        test_api();

        t_sum();
        fprintf(stderr, "%s\n", /* for at script */
            log_tst_no_cases_failed == 0 ? "PASS" : "FAIL");
    }
    else if (argc == 2 && !strcmp(argv[1], "run"))
        test_interactive();
    else printf("usage: test-datalog test|run\nrun for interactive mode");
}

/*int main(int argc, char** argv) { test_datalog(argc, argv); return 0; }*/

OVSTEST_REGISTER("test-datalog", test_datalog);

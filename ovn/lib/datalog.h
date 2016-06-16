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

#ifndef OVN_DATALOG_H
#define OVN_DATALOG_H 1

#include <stdbool.h>
#include <stdint.h>

/*
 * calling sequence:
 * init (put_table (put_field)*)* opr (get_table (get_field)*)* free
 *
 * init returns handle of the engine and will be used in all other calls.
 * put_table() returns false if table name is invalid.
 * size could be zero for put_field() and null-terminated c-str is assumed.
 * get_table() returns false if all tables have been retrieved.
 * get_field() returns false if the last tuple of a table has been retrieved.
 *
 * all values are assumed to be read only for both input and output.
 * see test_api for api examples.
 */

void* datalog_init(const char* rules, void* ext_func);
void  datalog_free(void* eng);

/* true for query and false for delta change */
void  datalog_opr(void* eng, bool query);

bool  datalog_put_table(void* eng, bool is_remove, const char* name);
void  datalog_put_field(void* eng, void* value, int32_t size);

bool  datalog_get_table(void* e, bool* is_remove, const char** name,
                       int32_t* n_tuples, int32_t* n_fields);
bool  datalog_get_field(void* e, void* v, int32_t* size);

#endif /* ovn_datalog.h */

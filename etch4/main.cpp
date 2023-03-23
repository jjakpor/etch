#include <float.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

#include <chrono>
#include <iostream>
#include <unordered_map>

#include "common.h"
#include "operators.h"
#include "sqlite3.h"

#define ETCH_TPCH 1
// #undef ETCH_MATH
// #undef ETCH_SQL

#ifdef ETCH_MATH
int dim = 10000;

#include "decls.c"

double threshold = 0.1;
#endif

#ifdef ETCH_TPCH
#include "decls_tpch.cpp"
#endif

static void sqlite_udf(sqlite3_context *context, int argc, sqlite3_value **argv) {
  int a = sqlite3_value_int(argv[0]);
  int b = sqlite3_value_int(argv[1]);
  double result = sqrt(abs(a - b));
  sqlite3_result_double(context, result);
}

//static inline double    nat_udf(int a, int b) {  /*printf("|%d,%d:%f|", a, b, sqrt(abs(a+b)));*/ return sqrt(abs(a + b)); }
static inline double    nat_udf_max(int a, int b) { return sqrt(abs(a - b)); }

static inline double* index_str_map(std::unordered_map<const char*, double>& m, const char* s) { return &m[s]; }


#ifdef ETCH_MATH
int i1_;
int i2_;
int i3_;
int j1_;
int j2_;
int j3_;
int k1_;
int k2_;
int k3_;
#endif

int temp;
bool not_done;
int hi;
int lo;
int m;
int out = 0;
double fout = 0.;


  //printf("reading : %d\n", atoi(argv[0]));
  //printf("reading : %d\n", atoi(argv[1]));
  //printf("reading : %f\n", atof(argv[2]));
static int noop(void *data, int argc, char **argv, char **azColName){
return 0;
}
static int print0(void *data, int argc, char **argv, char **azColName){
printf("reading : %d\n", atoi(argv[0]));
return 0;
}

#ifdef ETCH_MATH

static int gen_callback_graph_ssA(void *data, int argc, char **argv, char **azColName){
#include "gen_query_ssA.c"
return 0;
}

static int gen_callback_graph_dsA(void *data, int argc, char **argv, char **azColName){
#include "gen_query_dsA.c"
return 0;
}

static int gen_callback_graph_ssB(void *data, int argc, char **argv, char **azColName){
#include "gen_query_ssB.c"
return 0;
}

static int gen_callback_graph_dsB(void *data, int argc, char **argv, char **azColName){
#include "gen_query_dsB.c"
return 0;
}

static int gen_callback_graph_sssC(void *data, int argc, char **argv, char **azColName){
#include "gen_query_sssC.c"
return 0;
}
static int gen_callback_graph_dV(void *data, int argc, char **argv, char **azColName){
#include "gen_query_dV.c"
return 0;
}
static int gen_callback_graph_sV(void *data, int argc, char **argv, char **azColName){
#include "gen_query_sV.c"
return 0;
}

static int gen_callback_wcoj_R(void *data, int argc, char **argv, char **azColName){
#include "gen_query_wcoj_R.c"
return 0;
}
static int gen_callback_wcoj_S(void *data, int argc, char **argv, char **azColName){
#include "gen_query_wcoj_S.c"
return 0;
}
static int gen_callback_wcoj_T(void *data, int argc, char **argv, char **azColName){
#include "gen_query_wcoj_T.c"
return 0;
}
#endif // ETCH_MATH

static sqlite3* db;

#ifdef ETCH_SQL
static int count___ = 0;
static int count_callback(void *data, int argc, char **argv, char **azColName){
  printf("\n!!\n");
  count___ = atoi(argv[0]);
  return 0;
}
static int gen_callback_fires(void *data, int argc, char **argv, char **azColName){
#include "gen_query_fires.c"
return 0;
}
static int gen_callback_udf(void *data, int argc, char **argv, char **azColName){
  printf("udf result: %s\n", argv[0]);
return 0;
}

double sql_count_range_() {
  char* zErrMsg = 0;
  char* data;
  char const* sql = "(select * from fires order by objectid limit 10000)";
  count___ = 0;
  sqlite3_exec(db, sql, count_callback, (void*)data, &zErrMsg);
  //printf("HUH: %d\n",
  return count___;
}
#endif // ETCH_SQL

static int callback(void *data, int argc, char **argv, char **azColName){
   for(int i = 0; i<argc; i++){
      printf("%s = %s\n", azColName[i], argv[i] ? argv[i] : "NULL");
   }

   printf("\n");
   return 0;
}

// breakpoints
void start() { }
void done() { }

#include "gen_funs.c"

void load_data_of_size(sqlite3* db, int limit)
{
  char sql[256];
  //char const*sq;
  char* zErrMsg = 0;
  int rc;
  char* data;

#ifdef ETCH_SQL
    sprintf(sql, "SELECT * from (select * from graph1 order by val limit %d) ORDER BY src, tgt", limit);
    ssA1_pos[1] = 0;
    ssB1_pos[1] = 0;
    rc = sqlite3_exec(db, sql, gen_callback_graph_ssA, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, gen_callback_graph_dsA, (void*)data, &zErrMsg);
    //sq = "SELECT * from graph2 ORDER BY src, tgt";
    sprintf(sql, "SELECT * from (select * from graph2 order by val limit %d) ORDER BY src, tgt", limit);
    rc = sqlite3_exec(db, sql, gen_callback_graph_ssB, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, gen_callback_graph_dsB, (void*)data, &zErrMsg);
    //printf("loading C\n");
    /* load C */
    sprintf(sql, "SELECT * from (select * from c order by val limit %d) ORDER BY i, j, k", limit);
    rc = sqlite3_exec(db, sql, gen_callback_graph_sssC, (void*)data, &zErrMsg);
    /* load V */
    sprintf(sql, "SELECT * from (select * from v order by val limit %d) ORDER BY i", limit);
    rc = sqlite3_exec(db, sql, gen_callback_graph_dV, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, gen_callback_graph_sV, (void*)data, &zErrMsg);
#endif // ETCH_SQL

}

//void test_sample_mv(sqlite3* db) {
//  load_data_of_size(db, 100000);
//
//  double limits[] = {0, 0.2, 0.4, 0.6, 0.8, 1.0};
//  for(int i = 0; i < 6; i++) {
//    printf("testing thresh %f\n", limits[i]);
//    threshold = limits[i];
//    time(&filter_spmv, "etch", 10);
//  }
//}

#ifdef ETCH_MATH
void test_taco(sqlite3* db) {
  char sql[256];
  //char const*sq;
  char* zErrMsg = 0;
  int rc;
  char* data;

  //int sizes[] = {1000, 10000, 20000, 50000, 100000};
  int sizes[] = {50000};
  for(int i = 0; i < 1; i++) {
    printf("TESTING SIZE: %d\n\n", sizes[i]);
    load_data_of_size(db, sizes[i]);
#include "gen_out_taco.c"
  }
}
#endif

#ifdef ETCH_SQL
void test_sql(sqlite3* db) {
  char sql[256];
  //char const*sq;
  char* zErrMsg = 0;
  int rc;
  char* data;

  int sizes[] = {1000, 10000, 20000, 50000, 100000};
  sprintf(sql, "SELECT MAX(udf(a,b)) from R ");
  auto t1 = std::chrono::high_resolution_clock::now();
  rc = sqlite3_exec(db, sql, gen_callback_udf, (void*)data, &zErrMsg);
  if (rc) printf("\nNOT OK: %s\n", zErrMsg);
  auto t2 = std::chrono::high_resolution_clock::now();
  //std::cout << "val: " << val << std::endl;
  std::cout << "sql took: " << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl;
}
#endif
int main() {
  char* zErrMsg = 0;
  int rc = SQLITE_OK;
  char* data;

  sqlite3_initialize();
#ifdef ETCH_SQL
  rc = sqlite3_open("/home/scott/Dropbox/2022/pldi.db", &db);
#endif
#ifdef ETCH_TPCH
  rc = sqlite3_open("TPC-H.db", &db);
#endif

  if(rc) { fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db)); return(0);
  } else { fprintf(stderr, "Opened database successfully\n");
  }

  char const* sql;
  //sql = "SELECT * from (select * from graph1 order by val limit 100000) ORDER BY src, tgt";
  //rc = sqlite3_exec(db, sql, gen_callback_graph_ssA, (void*)data, &zErrMsg);
  //rc = sqlite3_exec(db, sql, gen_callback_graph_dsA, (void*)data, &zErrMsg);
  //sql = "SELECT * from graph2 ORDER BY src, tgt";
  //rc = sqlite3_exec(db, sql, gen_callback_graph_ssB, (void*)data, &zErrMsg);
  //rc = sqlite3_exec(db, sql, gen_callback_graph_dsB, (void*)data, &zErrMsg);


  //test_sample_mv(db);
  //return 0;

#ifdef ETCH_TPCH
  // populate_tpch(db);
  time([]() { return populate_tpch(db); }, "populate_tpch", 1);
  printf("Loaded\n");
#endif

  // HEY
#ifdef ETCH_MATH
  test_taco(db);
#endif

  //sqlite3_close(db);

#ifdef ETCH_SQL
  rc = sqlite3_exec(db, "SELECT * from R order by A, B", gen_callback_wcoj_R, (void*)data, &zErrMsg);
  if (rc) printf("nope");
  rc = sqlite3_exec(db, "SELECT * from S order by B, C", gen_callback_wcoj_S, (void*)data, &zErrMsg);
  if (rc) printf("nope");
  rc = sqlite3_exec(db, "SELECT * from T order by A, C", gen_callback_wcoj_T, (void*)data, &zErrMsg);
  if (rc) printf("nope");

  if (false) {
    sqlite3_open("/home/scott/Dropbox/2022/etch/etch4/data/FPA_FOD_20170508.sqlite", &db);
    if(rc) { fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db)); return(1);
    } else { fprintf(stderr, "Opened database successfully\n"); }
    //sql = "SELECT stat_cause_code, objectid from fires ORDER BY stat_cause_code, objectid LIMIT 100";
    //sql = "SELECT stat_cause_code, fire_year from fires ORDER BY stat_cause_code, fire_year LIMIT 100";
    sql = "SELECT fire_year, objectid from (select * from fires order by objectid limit 50000) ORDER BY fire_year, objectid";
    rc = sqlite3_exec(db, sql, gen_callback_fires, (void*)data, &zErrMsg);
    sql = "insert into fires_small SELECT fire_year, objectid from (select * from fires order by objectid limit 10000) ORDER BY fire_year, objectid";
    rc = sqlite3_exec(db, "DELETE FROM fires_small", noop, (void*)data, &zErrMsg);
    rc = sqlite3_exec(db, sql, noop, (void*)data, &zErrMsg);
  }

  sqlite3_create_function(db, "udf", 2, SQLITE_UTF8, NULL, &sqlite_udf, NULL, NULL);

  if( rc != SQLITE_OK ) {
     fprintf(stderr, "SQL error: %s\n", zErrMsg);
     sqlite3_free(zErrMsg);
     return 1;
  } else {
     fprintf(stdout, "Operation done successfully\n");
  }
#endif
  start();

#ifdef ETCH_TPCH
  time(q5, "q5", 5);
#endif

#ifdef ETCH_MATH
  printf("the answer: %f\n", taco_wcoj());
#endif

  //HEY
  //test_sql(db);

// warmup?
//  fout = 0;
//#include "gen_main.c"
//  taco_mul2();
// warmup

  // decl
  //auto t1 = std::chrono::high_resolution_clock::now();
  //auto t2 = std::chrono::high_resolution_clock::now();
  //int reps = 100;
  //double tout;
  //double val;

  //printf("count_range_sql:\n");
  //auto t1 = std::chrono::high_resolution_clock::now();
  //sql = "select COUNT(*) from fires_small WHERE 2006 <= fire_year and fire_year < 2007";
  //sqlite3_exec(db, sql, print0, (void*)data, &zErrMsg);
  //auto t2 = std::chrono::high_resolution_clock::now();
  ////std::cout << "val: " << val << std::endl;
  //std::cout << " took: " << std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count() << "μ" << std::endl;
  //std::cout << " took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count() << "ms" << std::endl;

  done();

// #include "gen_out.c"

  sqlite3_close(db);
  return 0;
}

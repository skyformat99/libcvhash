/*
 *   oryx_assert.h
 *   Created by TSIHANG <qh_soledadboy@sina.com>>
 *   1 June, 2015
 *   Personal.Q
 */


#ifndef __ORYX_ASSERT_H__
#define __ORYX_ASSERT_H__

extern void abts_ptr_notnull(const void *ptr, int lineno);
extern void abts_int_equal(const int expected, const int actual, int lineno);
extern void abts_int_nequal(const int expected, const int actual, int lineno);
extern void abts_size_equal(size_t expected, size_t actual, int lineno);
extern void abts_str_equal(const char *expected, const char *actual, int lineno);
extern void abts_str_nequal(const char *expected, const char *actual,
                       size_t n, int lineno);
extern void abts_ptr_equal(const void *expected, const void *actual, int lineno);
extern void abts_assert(const char *message, int condition, int lineno);
extern void abts_true(int condition, int lineno);
extern void abts_not_impl(const char *message, int lineno);
extern void abts_fail(const char *message, int lineno);

extern void oryx_assert_success(const char* context, apr_status_t rv,
                   int __oryx_unused__ lineno);
extern void oryx_assert_failure(const char* context, apr_status_t rv,
                        int lineno);

#define ORYX_ASSERT_SUCCESS(ctxt, rv) \
             oryx_assert_success(ctxt, rv, __LINE__)
             
#define ABTS_INT_EQUAL(b, c)     abts_int_equal(b, c, __LINE__)
#define ABTS_INT_NEQUAL(b, c)    abts_int_nequal(b, c, __LINE__)
#define ABTS_STR_EQUAL(b, c)     abts_str_equal(b, c, __LINE__)
#define ABTS_STR_NEQUAL(b, c, d) abts_str_nequal(b, c, d, __LINE__)
#define ABTS_PTR_NOTNULL(b)      abts_ptr_notnull(b, __LINE__)
#define ABTS_PTR_EQUAL(b, c)     abts_ptr_equal(b, c, __LINE__)
#define ABTS_TRUE(b)             abts_true(b, __LINE__);
#define ABTS_FAIL(b)             abts_fail(b, __LINE__);
#define ABTS_NOT_IMPL(b)         abts_not_impl(b, __LINE__);
#define ABTS_ASSERT(b, c)        abts_assert(b, c, __LINE__);
#define ABTS_SUCCESS(rv)    	ABTS_INT_EQUAL(APR_SUCCESS, rv)

#endif


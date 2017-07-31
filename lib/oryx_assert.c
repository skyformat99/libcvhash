
#include "oryx.h"
#include "oryx_error.h"
#include "oryx_assert.h"

int verbose = 1;

void abts_ptr_notnull(const void *ptr, int __oryx_unused__ lineno)
{

    if (ptr != NULL) return;

    if (verbose) {
        //oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected non-NULL, but saw NULL\n", lineno);
        fflush(stderr);
    }
}

void abts_int_equal(const int expected, const int actual, int __oryx_unused__ lineno)
{
    if (expected == actual) return;

    if (verbose) {
        //oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected <%d>, but saw <%d>\n", lineno, expected, actual);
        fflush(stderr);
    }
}

void abts_int_nequal(const int expected, const int actual, int __oryx_unused__ lineno)
{
    if (expected != actual) return;

    if (verbose) {
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected something other than <%d>, but saw <%d>\n",
                lineno, expected, actual);*/
        fflush(stderr);
    }
}

void abts_size_equal(size_t expected, size_t actual, int __oryx_unused__ lineno)
{
    if (expected == actual) return;

    if (verbose) {
        /* Note that the comparison is type-exact, reporting must be a best-fit */
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected %lu, but saw %lu\n", lineno, 
                (unsigned long)expected, (unsigned long)actual);*/
        fflush(stderr);
    }
}

void abts_str_equal(const char *expected, const char *actual, int __oryx_unused__ lineno)
{
    if (!expected && !actual) return;
    if (expected && actual)
        if (!strcmp(expected, actual)) return;

    if (verbose) {
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected <%s>, but saw <%s>\n", lineno, expected, actual);*/
        fflush(stderr);
    }
}

void abts_str_nequal(const char *expected, const char *actual,
                       size_t n, int __oryx_unused__ lineno)
{

    if (!strncmp(expected, actual, n)) return;

    if (verbose) {
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected something other than <%s>, but saw <%s>\n",
                lineno, expected, actual);*/
        fflush(stderr);
    }
}

void abts_ptr_equal(const void *expected, const void *actual, int __oryx_unused__ lineno)
{
    if (expected == actual) return;

    if (verbose) {
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: expected <%p>, but saw <%p>\n", lineno, expected, actual);
        fflush(stderr);*/
    }
}

void abts_fail(const char *message, int __oryx_unused__ lineno)
{
    if (verbose) {
	message = message;
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: %s\n", lineno, message);*/
        fflush(stderr);
    }
}

void abts_not_impl(const char *message, int __oryx_unused__ lineno)
{
    if (verbose) {
	message = message;
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: %s\n", lineno, message);*/
        fflush(stderr);
    }
}

void abts_assert(const char *message, int condition, int __oryx_unused__ lineno)
{

    if (condition) return;

    if (verbose) {
	message = message;
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: %s\n", lineno, message);*/
        fflush(stderr);
    }
}

void abts_true(int condition, int __oryx_unused__ lineno)
{
    if (condition) return;

    if (verbose) {
        /**oryx_log_warning(ERRNO_INVALID_VAL, "Line %d: Condition is false, but expected true\n", lineno);*/
        fflush(stderr);
    }
}

void oryx_assert_success(const char* context, apr_status_t rv,
                        int __oryx_unused__ lineno)
{
    if (rv == APR_ENOTIMPL) {
        ABTS_NOT_IMPL(context);
    }

    if (rv != APR_SUCCESS) {
        char buf[STRING_MAX], ebuf[128];
        sprintf (buf, "%s (%d): %s\n", context, rv,
                apr_strerror(rv, ebuf, sizeof ebuf));
        ABTS_FAIL(buf);
    }
}

void oryx_assert_failure(const char* context, apr_status_t rv,
                        int __oryx_unused__ lineno)
{
    if (rv == APR_ENOTIMPL) {
        abts_not_impl(context, lineno);
    } else if (rv == APR_SUCCESS) {
        char buf[STRING_MAX];
        sprintf(buf, "%s (%d): expected failure, got success\n", context, rv);
        abts_fail(buf, lineno);
    }
}

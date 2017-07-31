/*
 *   oryx_ipc.c
 *   Created by TSIHANG <qh_soledadboy@sina.com>>
 *   1 June, 2015
 *   Personal.Q
 */


#include "oryx.h"
#include "oryx_ipc.h"
#include "oryx_assert.h"

static oryx_pool_t *sync_pool = NULL;

oryx_status_t oryx_thread_mutex_create(oryx_thread_mutex_t **mutex)
{
	if (!sync_pool) {
		apr_pool_create(&sync_pool, NULL);
		ABTS_PTR_NOTNULL (sync_pool);
		printf ("Sync pool allocate success\n");
	}

	apr_thread_mutex_create (mutex, APR_THREAD_MUTEX_DEFAULT, sync_pool);
	ABTS_PTR_NOTNULL (*mutex);

	return APR_SUCCESS;
}

oryx_status_t oryx_thread_cond_create(oryx_thread_cond_t **cond)
{
	if (!sync_pool) {
		apr_pool_create(&sync_pool, NULL);
		ABTS_PTR_NOTNULL (sync_pool);
	}

	apr_thread_cond_create (cond, sync_pool);
	ABTS_PTR_NOTNULL (*cond);

	return APR_SUCCESS;
}



/*
*   oryx_ipc.h
*   Created by TSIHANG <qh_soledadboy@sina.com>
*   1 June, 2015
*   Func: Synchronous operation interface
*   Personal.Q
*/


#ifndef __ORYX_IPC_H__
#define __ORYX_IPC_H__

#define INIT_MUTEX_VAL	{NULL, PTHREAD_MUTEX_INITIALIZER}
#define INIT_COND_VAL	{NULL, PTHREAD_COND_INITIALIZER}

#define INIT_MUTEX(name)\
    oryx_thread_mutex_t name = INIT_MUTEX_VAL;

#define INIT_COND(name)\
    oryx_thread_cond_t name = INIT_COND_VAL;

extern oryx_status_t oryx_thread_mutex_create(oryx_thread_mutex_t **mutex);
extern oryx_status_t oryx_thread_cond_create(oryx_thread_cond_t **cond);

#define oryx_thread_mutex_destroy(mptr)\
		apr_thread_mutex_destroy(mptr)
		
#define oryx_thread_mutex_lock(mptr)\
		apr_thread_mutex_lock(mptr)

#define oryx_thread_mutex_trylock(mptr)\
		apr_thread_mutex_trylock(mptr)
		
#define oryx_thread_mutex_unlock(mptr)\
		apr_thread_mutex_unlock(mptr)

#define oryx_thread_cond_wait(c,mptr)\
		apr_thread_cond_wait(c,mptr)

#define oryx_thread_cond_timedwait(c,mptr,t)\
		apr_thread_cond_timedwait(c,mptr,t)
		
#define oryx_thread_cond_signal(cptr)\
		apr_thread_cond_signal(cptr)
	
#define oryx_thread_cond_broadcast(cptr)\
		apr_thread_cond_broadcast(cptr)


#define rt_spinlock                                                 pthread_spinlock_t
#define rt_spinlock_lock(spin)                              pthread_spin_lock(spin)
#define rt_spinlock_trylock(spin)                     pthread_spin_trylock(spin)
#define rt_spinlock_unlock(spin)                      pthread_spin_unlock(spin)
#define rt_spinlock_init(spin, spin_attr)             pthread_spin_init(spin, spin_attr)
#define rt_spinlock_destroy(spin)                     pthread_spin_destroy(spin)


#endif


/*
 *   oryx_config.h
 *   Created by TSIHANG <qh_soledadboy@sina.com>>
 *   1 June, 2015
 *   Personal.Q
 */

#ifndef __ORYX_CONFIG_H__
#define __ORYX_CONFIG_H__

#define ORYX_HAVE_FAXTOOL	0
#define ORYX_HAVE_ADVANCED_TMR	1

#define ORYX_HAVE_MEMPOOL	1

/* Are we big endian? */
#define ORYX_IS_BIGENDIAN	0

#define ORYX_HAVE_SHMEM_MMAP_TMP     1
#define ORYX_HAVE_SHMEM_MMAP_SHM     1
#define ORYX_HAVE_SHMEM_MMAP_ZERO    1
#define ORYX_HAVE_SHMEM_SHMGET_ANON  1
#define ORYX_HAVE_SHMEM_SHMGET       1
#define ORYX_HAVE_SHMEM_MMAP_ANON    1
#define ORYX_HAVE_SHMEM_BEOS         0

#define ORYX_USE_SHMEM_MMAP_TMP     0
#define ORYX_USE_SHMEM_MMAP_SHM     0
#define ORYX_USE_SHMEM_MMAP_ZERO    0
#define ORYX_USE_SHMEM_SHMGET_ANON  0
#define ORYX_USE_SHMEM_SHMGET       1
#define ORYX_USE_SHMEM_MMAP_ANON    1
#define ORYX_USE_SHMEM_BEOS         0

#define ORYX_USE_FLOCK_SERIALIZE           0 
#define ORYX_USE_SYSVSEM_SERIALIZE         1
#define ORYX_USE_POSIXSEM_SERIALIZE        0
#define ORYX_USE_FCNTL_SERIALIZE           0
#define ORYX_USE_PROC_PTHREAD_SERIALIZE    0 
#define ORYX_USE_PTHREAD_SERIALIZE         1 

/*  ORYX Runtime Platform Feature Macros */
#define ORYX_HAS_FLOCK_SERIALIZE           1
#define ORYX_HAS_SYSVSEM_SERIALIZE         1
#define ORYX_HAS_POSIXSEM_SERIALIZE        1
#define ORYX_HAS_FCNTL_SERIALIZE           1
#define ORYX_HAS_PROC_PTHREAD_SERIALIZE    1

#define ORYX_PROCESS_LOCK_IS_GLOBAL        0

#define ORYX_HAVE_CORKABLE_TCP   1 
#define ORYX_HAVE_GETRLIMIT      1
#define ORYX_HAVE_IN_ADDR        1
#define ORYX_HAVE_INET_ADDR      1
#define ORYX_HAVE_INET_NETWORK   1
#define ORYX_HAVE_IPV6           1
#define ORYX_HAVE_MEMMOVE        1
#define ORYX_HAVE_SETRLIMIT      1
#define ORYX_HAVE_SIGACTION      1
#define ORYX_HAVE_SIGSUSPEND     1
#define ORYX_HAVE_SIGWAIT        1
#define ORYX_HAVE_SA_STORAGE     1
#define ORYX_HAVE_STRCASECMP     1
#define ORYX_HAVE_STRDUP         1
#define ORYX_HAVE_STRICMP        0
#define ORYX_HAVE_STRNCASECMP    1
#define ORYX_HAVE_STRNICMP       0
#define ORYX_HAVE_STRSTR         1
#define ORYX_HAVE_MEMCHR         1
#define ORYX_HAVE_STRUCT_RLIMIT  1
#define ORYX_HAVE_UNION_SEMUN    0
#define ORYX_HAVE_SCTP           0
#define ORYX_HAVE_IOVEC          1

/*  ORYX Feature Macros */
#define ORYX_HAS_SHARED_MEMORY     1
#define ORYX_HAS_THREADS           1
#define ORYX_HAS_SENDFILE          1
#define ORYX_HAS_MMAP              1
#define ORYX_HAS_FORK              1
#define ORYX_HAS_RANDOM            1
#define ORYX_HAS_OTHER_CHILD       1
#define ORYX_HAS_DSO               1
#define ORYX_HAS_SO_ACCEPTFILTER   0
#define ORYX_HAS_UNICODE_FS        0
#define ORYX_HAS_PROC_INVOKED      0
#define ORYX_HAS_USER              1
#define ORYX_HAS_LARGE_FILES       0
#define ORYX_HAS_XTHREAD_FILES     0
#define ORYX_HAS_OS_UUID           0


#define BRANCH_SDKLIB		0x01
#define BRANCH_STANDALONE	0x02


#endif

/*
 *   oryx.h
 *   Created by TSIHANG <qh_soledadboy@sina.com>>
 *   1 June, 2015
 *   Personal.Q
 */

#ifndef __ORYX_H__
#define __ORYX_H__

#include "oryx_config.h"
#include "apr.h"
#include "apr_arch_thread_mutex.h"
#include "apr_arch_thread_cond.h"
#include "apr_arch_file_io.h"
#include "apr_arch_networkio.h"

#include "apr_thread_mutex.h"
#include "apr_thread_cond.h"
#include "apr_file_io.h"
#include "apr_network_io.h"
#include "apr_signal.h"
#include "apr_file_io.h"
#include "apr_dbd.h"
#include "apr_md5.h"


#if 1
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#ifndef __USE_GNU
#define __USE_GNU
#endif

#define __STDC_FORMAT_MACRO

#ifndef HAVE_LIMITS_H
#define HAVE_LIMITS_H 1
#endif

#ifdef HAVE_STDIO_H
#include <stdio.h>
#endif

#ifdef HAVE_STDINT_h
#include <stdint.h>
#endif

#ifdef HAVE_STDDEF_H
#include <stddef.h>
#endif

#ifdef HAVE_STDBOOL_H
#include <stdbool.h>
#endif

#ifdef HAVE_STDARG_H
#include <stdarg.h>
#endif

#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif

#ifdef HAVE_ERRNO_H
#include <errno.h>
#endif

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#ifdef HAVE_ASSERT_H
#include <assert.h>
#endif

#ifdef HAVE_INTTYPES_H
#include <inttypes.h>
#endif

#ifdef HAVE_LIMITS_H
#include <limits.h>
#endif

#ifdef HAVE_CTYPE_H
#include <ctype.h>
#endif

#ifdef HAVE_STRING_H
#include <string.h>
#endif

#ifdef HAVE_STRINGS_H
#include <strings.h>
#endif

#ifdef HAVE_FCNTL_H
#include <fcntl.h>
#endif

#ifdef HAVE_TIME_H
#include <time.h>
#endif

#include <syscall.h>
#include <semaphore.h>
#include <netdb.h>
#include <dirent.h>
#include <mntent.h>

#include <regex.h>
#include <getopt.h>
#include <pcre.h>
#include <sys/epoll.h>
#include <sys/resource.h>
#include <sys/wait.h>

#if HAVE_SYS_SYSCALL_H
#include <sys/syscall.h>
#endif

#if HAVE_SYSCALL_H
#include <syscall.h>
#endif

#if HAVE_SYS_TYPES_H
#include <sys/types.h> /* for gettid(2) */
#endif

#if HAVE_SCHED_H
#include <sched.h>     /* for sched_setaffinity(2) */
#endif

#ifdef HAVE_SYSLOG_H
#include <syslog.h>
#endif /* HAVE_SYSLOG_H */

#if HAVE_SIGNAL_H
#include <signal.h>
#endif

#if HAVE_POLL_H
#include <poll.h>
#endif

#if HAVE_SYS_SIGNAL_H
#include <sys/signal.h>
#endif

#if HAVE_SYS_TYPES_H
#include <sys/types.h>
#endif

#if HAVE_SYS_STAT_H
#include <sys/stat.h>
#endif

#include <sys/un.h>

#if HAVE_SYS_SOCKET_H
#include <sys/socket.h>
#endif

#include <sys/stat.h>

#if HAVE_SYS_TIME_H
#include <sys/time.h>
#endif

#if HAVE_NETINET_IN_H
#include <netinet/in.h>
#endif

#ifdef HAVE_NETINET_TCP_H
#include <netinet/tcp.h>
#endif

#if HAVE_ARPA_INET_H
#include <arpa/inet.h>
#endif

#if HAVE_NETDB_H
#include <netdb.h>
#endif

#ifdef HAVE_PCAP_H
#include <pcap.h>
#endif

#ifdef HAVE_PCAP_PCAP_H
#include <pcap/pcap.h>
#endif

#ifdef HAVE_PCAP_BPF_H
#include <pcap/bpf.h>
#endif

#include <assert.h>

#ifdef __linux__
#include <unistd.h>
#endif
#endif

#include <sys/ioctl.h>

#include <linux/sockios.h>
#include <net/if.h>

#include <sys/time.h>

#ifndef reserved
#define	RESERVED	(-1)
#endif

#ifndef VALID
#define VALID 1
#define INVALID 0
#endif

#ifndef uninitialized
#define UNINIT 0
#define INITED 1
#endif

#ifndef ENABLE
#define ENABLE  1
#define DISABLE 0
#endif

#ifndef FOREVER
#define FOREVER for(;;)
#endif

#ifndef IN
#define IN
#define OUT
#endif

#ifndef THIS_API_IS_ONLY_FOR_TEST
#define THIS_API_IS_ONLY_FOR_TEST
#endif

#ifndef The_interface_has_not_been_tested
#define The_interface_has_not_been_tested
#define THE_INTERFACE_HAS_NOT_BEEN_TESTED
#endif

#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif
#ifndef MIN
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#endif

#define declare_array(type, name, size)  type name[size] = {0}
#define declare_variable(type, name, val)  type name = val

#define EVAL_TM_STYLE_YH   "%Y%m%d%H"
#define EVAL_TM_STYLE_YD   "%Y%m%d"

#define EVAL_TM_STYLE   "%Y-%m-%d"
#define EVAL_TM_STYLE_EXT   "%H:%M:%S"
#define EVAL_TM_STYLE_FULL "%Y-%m-%d %H:%M:%S"
#define EVAL_FILE_PATH  "/home/tsihang/eval/db4spasr"


/** Alway treated the expr as true */
#ifndef likely
#define likely(expr) __builtin_expect(!!(expr), 1)
#endif

/** Alway treated the expr as false */
#ifndef unlikely
#define unlikely(expr) __builtin_expect(!!(expr), 0)
#endif

extern int errno;
#ifndef ERRNO_EQUAL
#define ERRNO_EQUAL(e) (errno == e)
#endif

#define THIS 0

enum {
    ALLOWED, 
    FORBIDDEN
}; 

#ifndef offsetof
#define offsetof(type, member) ((size_t) &((type *)0)->member)
#endif

#ifndef container_of
#define container_of(ptr, type, member) ({ \
        const typeof(((type *)0)->member) *__mptr = (ptr); \
        (type *)((char *)__mptr - offsetof(type,member));})
#endif

#define	__oryx_always_inline__	__attribute__((__always_inline__)) inline
#define	__oryx_unused__		__attribute__((unused))

/* we need this to stringify the defines which are supplied at compiletime see:
   http://gcc.gnu.org/onlinedocs/gcc-3.4.1/cpp/Stringification.html#Stringification */
#define xstr(s) str(s)
#define str(s) #s

#include <stdint.h>
#include <unistd.h>

#define BUG_ON(chk) assert (!(chk));

typedef unsigned char	oryx_byte_t;
typedef apr_ssize_t	oryx_ssize_t;
typedef apr_size_t	oryx_size_t;
typedef size_t		oryx_size_t;
typedef int16_t		oryx_int16_t;
typedef uint8_t		oryx_uint8_t;
typedef uint16_t	oryx_uint16_t;
typedef uint32_t	oryx_uint32_t;
typedef int32_t		oryx_int32_t;
typedef uint64_t	oryx_uint64_t;
typedef int64_t		oryx_int64_t;
typedef off_t		oryx_off_t;
typedef socklen_t	oryx_socklen_t;
typedef oryx_uint16_t	oryx_port_t;

typedef oryx_uint32_t		HASH_INDEX;

typedef apr_pool_t			oryx_pool_t;
typedef apr_os_thread_t		oryx_os_thread_t;
typedef apr_thread_t		oryx_thread_t ;

typedef	apr_thread_cond_t	oryx_thread_cond_t;
typedef	apr_thread_mutex_t	oryx_thread_mutex_t;
typedef apr_threadkey_t		oryx_threadkey_t;   /**< native thread address
                                                     *   space */
typedef	apr_os_file_t		oryx_os_file_t;
typedef apr_file_t			oryx_file_t;
typedef apr_os_dir_t		oryx_os_dir_t;         /**< native dir */
typedef apr_dir_t			oryx_dir_t;
typedef apr_os_sock_t		oryx_os_sock_t;
typedef apr_int32_t			oryx_os_poll_handle_t;
typedef	apr_socket_t		oryx_socket_t;
typedef apr_os_proc_t		oryx_os_proc_t;        /**< native pid */
typedef apr_proc_t			oryx_proc_t;

typedef struct timeval		oryx_os_imp_time_t;    /**< native timeval */
typedef struct tm			oryx_os_exp_time_t;    /**< native tm */
typedef apr_interval_time_t	oryx_interval_time_t;

typedef void *			oryx_os_dso_handle_t;
typedef void *			oryx_os_shm_t;         /**< native SHM */
typedef  ino_t          oryx_ino_t;
typedef oryx_int32_t	oryx_status_t;


#define GETL_BYTE2(p)		(((p)[0]<<8)  | (p)[1])
#define GETL_BYTE3(p)		(((p)[0]<<16) | ((p)[1]<<8)  | (p)[2])
#define GETL_BYTE4(p)		(((p)[0]<<24) | ((p)[1]<<16) | ((p)[2]<<8) | (p)[3])

#define ADDR_OFFSETOF(addr, bytes) ((addr>>(bytes*8))&0x000000FF)

typedef uint16_t port_t;

/* Network address indicated for protocol header. */
typedef union {
	uint8_t	 val8[16];
	uint32_t val32[4];
	uint64_t val64[2];
	struct{
		uint32_t    v4;
		uint32_t    r;
	};

	struct {
	    uint64_t    v6u;	/** Upper */
	    uint64_t    v6l;	/** Lower */
	};
} ip_addr_t;

/* Address */
struct inet_addr {
    char family;
    union {
        uint32_t       data32[4]; /* type-specific field */
        uint16_t       data16[8]; /* type-specific field */
        uint8_t        data8[16]; /* type-specific field */
    } address;
};

struct oryx_os_sock_info_t {
	oryx_os_sock_t *os_sock; /**< always required */
	struct sockaddr *local; /**< NULL if not yet bound */
	struct sockaddr *remote; /**< NULL if not connected */
	int family;             /**< always required (AF_INET, AF_INET6, etc.) */
	int type;               /**< always required (SOCK_STREAM, SOCK_DGRAM, etc.) */
	int protocol;           /**< 0 or actual protocol (AF_PROTO_SCTP, AF_PROTO_TCP, etc.) */
};

/** @remark It's defined here as I think it should all be platform safe...
 * @see oryx_sockaddr_t
 */
typedef struct apr_sockaddr_t oryx_sockaddr_t;

/**
 * Alignment macros
 */

/* ORYX_ALIGN() is only to be used to align on a power of 2 boundary */
#define ORYX_ALIGN(size, boundary) \
    (((size) + ((boundary) - 1)) & ~((boundary) - 1))

/** Default alignment */
#define ORYX_ALIGN_DEFAULT(size) ORYX_ALIGN(size, 8)

/* temporary defines to handle 64bit compile mismatches */
#define ORYX_INT_TRUNC_CAST    int
#define ORYX_UINT32_TRUNC_CAST oryx_uint32_t

#define ORYX_DECLARE(type) type

/* Mechanisms to properly type numeric literals */
#define ORYX_INT64_C(val) INT64_C(val)
#define ORYX_UINT64_C(val) UINT64_C(val)


/** type for the internal signature id. Since it's used in the matching engine
 *  extensively keeping this as small as possible reduces the overall memory
 *  footprint of the engine. Set to uint32_t if the engine needs to support
 *  more than 64k sigs. */
//#define SigIntId uint16_t
#define SigIntId uint32_t

/** same for pattern id's */
#define PatIntId uint16_t

#define SCReturnInt(i) return (i)
#define SCEnter()	
#define SCReturn return
#define SCReturnPtr(x,d) return (x)



/** @} */

/**
 * @defgroup oryx_ctype ctype functions
 * These macros allow correct support of 8-bit characters on systems which
 * support 8-bit characters.  Pretty dumb how the cast is required, but
 * that's legacy libc for ya.  These new macros do not support EOF like
 * the standard macros do.  Tough.
 * @{
 */
/** @see isalnum */
#define oryx_isalnum(c) (isalnum(((unsigned char)(c))))
/** @see isalpha */
#define oryx_isalpha(c) (isalpha(((unsigned char)(c))))
/** @see iscntrl */
#define oryx_iscntrl(c) (iscntrl(((unsigned char)(c))))
/** @see isdigit */
#define oryx_isdigit(c) (isdigit(((unsigned char)(c))))
/** @see isgraph */
#define oryx_isgraph(c) (isgraph(((unsigned char)(c))))
/** @see islower*/
#define oryx_islower(c) (islower(((unsigned char)(c))))
/** @see isascii */
#ifdef isascii
#define oryx_isascii(c) (isascii(((unsigned char)(c))))
#else
#define oryx_isascii(c) (((c) & ~0x7f)==0)
#endif
/** @see isprint */
#define oryx_isprint(c) (isprint(((unsigned char)(c))))
/** @see ispunct */
#define oryx_ispunct(c) (ispunct(((unsigned char)(c))))
/** @see isspace */
#define oryx_isspace(c) (isspace(((unsigned char)(c))))
/** @see isupper */
#define oryx_isupper(c) (isupper(((unsigned char)(c))))
/** @see isxdigit */
#define oryx_isxdigit(c) (isxdigit(((unsigned char)(c))))
/** @see tolower */
#define oryx_tolower(c) (tolower(((unsigned char)(c))))
/** @see toupper */
#define oryx_toupper(c) (toupper(((unsigned char)(c))))

/** @} */


/* Macroes for conversion between host and network byte order */
#define hton8(x)  (x)
#define ntoh8(x)  (x)
#define hton16(x) htons(x)
#define ntoh16(x) ntohs(x)
#define hton32(x) htonl(x)
#define ntoh32(x) ntohl(x)

#ifndef INT_MAX
#define INT_MAX ((int)(~0U>>1))
#endif

#ifndef INT_MIN
#define INT_MIN (-INT_MAX - 1)
#endif

#ifndef UINT_MAX
#define UINT_MAX (~0U)
#endif

#ifndef LONG_MAX
#define LONG_MAX ((long)(~0UL>>1))
#endif

#ifndef LONG_MIN
#define LONG_MIN (-LONG_MAX - 1)
#endif

#ifndef ULONG_MAX
#define ULONG_MAX (~0UL)
#endif

#ifndef LLONG_MAX
#define LLONG_MAX ((long long)(~0ULL>>1))
#endif

#ifndef LLONG_MIN
#define LLONG_MIN (-LLONG_MAX - 1)
#endif

#ifndef ULLONG_MAX
#define ULLONG_MAX (~0ULL)
#endif


#define ORYX_INT32_MAX		INT_MAX
#define ORYX_INT32_MIN		INT_MIN
#define ORYX_UINT32_MAX		UINT_MAX

#define ORYX_THREAD_FUNC       

#if defined(DOXYGEN) || !defined(WIN32)

/**
 * The public ORYX functions are declared with ORYX_DECLARE(), so they may
 * use the most appropriate calling convention.  Public ORYX functions with 
 * variable arguments must use ORYX_DECLARE_NONSTD().
 *
 * @remark Both the declaration and implementations must use the same macro.
 *
 * <PRE>
 * ORYX_DECLARE(rettype) oryx_func(args)
 * </PRE>
 * @see ORYX_DECLARE_NONSTD @see ORYX_DECLARE_DATA
 * @remark Note that when ORYX compiles the library itself, it passes the 
 * symbol -DORYX_DECLARE_EXPORT to the compiler on some platforms (e.g. Win32) 
 * to export public symbols from the dynamic library build.\n
 * The user must define the ORYX_DECLARE_STATIC when compiling to target
 * the static ORYX library on some platforms (e.g. Win32.)  The public symbols 
 * are neither exported nor imported when ORYX_DECLARE_STATIC is defined.\n
 * By default, compiling an application and including the ORYX public
 * headers, without defining ORYX_DECLARE_STATIC, will prepare the code to be
 * linked to the dynamic library.
 */
#define ORYX_DECLARE(type)            type 

/**
 * The public ORYX functions using variable arguments are declared with 
 * ORYX_DECLARE_NONSTD(), as they must follow the C language calling convention.
 * @see ORYX_DECLARE @see ORYX_DECLARE_DATA
 * @remark Both the declaration and implementations must use the same macro.
 * <PRE>
 *
 * ORYX_DECLARE_NONSTD(rettype) oryx_func(args, ...);
 *
 * </PRE>
 */
#define ORYX_DECLARE_NONSTD(type)     type

/**
 * The public ORYX variables are declared with AP_MODULE_DECLARE_DATA.
 * This assures the appropriate indirection is invoked at compile time.
 * @see ORYX_DECLARE @see ORYX_DECLARE_NONSTD
 * @remark Note that the declaration and implementations use different forms,
 * but both must include the macro.
 * 
 * <PRE>
 *
 * extern ORYX_DECLARE_DATA type oryx_variable;\n
 * ORYX_DECLARE_DATA type oryx_variable = value;
 *
 * </PRE>
 */
#define ORYX_DECLARE_DATA

#elif defined(ORYX_DECLARE_STATIC)
#define ORYX_DECLARE(type)            type __stdcall
#define ORYX_DECLARE_NONSTD(type)     type __cdecl
#define ORYX_DECLARE_DATA
#elif defined(ORYX_DECLARE_EXPORT)
#define ORYX_DECLARE(type)            __declspec(dllexport) type __stdcall
#define ORYX_DECLARE_NONSTD(type)     __declspec(dllexport) type __cdecl
#define ORYX_DECLARE_DATA             __declspec(dllexport)
#else
#define ORYX_DECLARE(type)            __declspec(dllimport) type __stdcall
#define ORYX_DECLARE_NONSTD(type)     __declspec(dllimport) type __cdecl
#define ORYX_DECLARE_DATA             __declspec(dllimport)
#endif

/* Define ORYX_SSIZE_T_FMT.  
 * If ssize_t is an integer we define it to be "d",
 * if ssize_t is a long int we define it to be "ld",
 * if ssize_t is neither we declare an error here.
 * I looked for a better way to define this here, but couldn't find one, so
 * to find the logic for this definition search for "ssize_t_fmt" in
 * configure.in.
 */

#define ORYX_SSIZE_T_FMT "ld"

/* And ORYX_SIZE_T_FMT */
#define ORYX_SIZE_T_FMT "lu"

/* And ORYX_OFF_T_FMT */
#define ORYX_OFF_T_FMT "ld"

/* And ORYX_PID_T_FMT */
#define ORYX_PID_T_FMT "d"

/* And ORYX_INT64_T_FMT */
#define ORYX_INT64_T_FMT "ld"

/* And ORYX_UINT64_T_FMT */
#define ORYX_UINT64_T_FMT "lu"

/* And ORYX_UINT64_T_HEX_FMT */
#define ORYX_UINT64_T_HEX_FMT "lx"


#define ORYX_SIZEOF_VOIDP 8


#define VOID_POOL	void*

#ifndef FALSE
#define FALSE 0
#endif
#ifndef TRUE
#define TRUE 1
#endif

#define STRING_MAX 8096


#define CONSOLE_PRINT_CLOR_FIN			"\e[0m"
#define CONSOLE_PRINT_CLOR_BLK			"\e[0;30m"
#define CONSOLE_PRINT_CLOR_LBLK			"\e[1;30m"
#define CONSOLE_PRINT_CLOR_RED			"\e[0;31m"
#define CONSOLE_PRINT_CLOR_LRED			"\e[1;31m"
#define CONSOLE_PRINT_CLOR_YELLOW		"\e[0;33m"
#define CONSOLE_PRINT_CLOR_LYELLOW		"\e[1;33m"
#define CONSOLE_PRINT_CLOR_WHITE		"\e[0;37m"
#define CONSOLE_PRINT_CLOR_LWHITE		"\e[1;37m"



#define GREEN                "\e[0;32m"
#define L_GREEN              "\e[1;32m"
#define BROWN                "\e[0;33m"
#define BLUE                 "\e[0;34m"
#define L_BLUE               "\e[1;34m"
#define PURPLE               "\e[0;35m"
#define L_PURPLE             "\e[1;35m"
#define CYAN                 "\e[0;36m"
#define L_CYAN               "\e[1;36m"
#define GRAY                 "\e[0;37m"


#define BOLD                 "\e[1m"
#define UNDERLINE            "\e[4m"
#define BLINK                "\e[5m"
#define REVERSE              "\e[7m"
#define HIDE                 "\e[8m"
#define CLEAR                "\e[2J"
#define CLRLINE              "\r\e[K" //or "\e[1K\r"

#ifndef oryx_strcmp_native
#define oryx_strcmp_native(S,D) (strcmp((const char *)S,(const char *)D))
#endif


#endif	/* ORYX_H */

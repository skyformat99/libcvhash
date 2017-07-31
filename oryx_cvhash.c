/*
 *   oryx_vchash.c
 *   Created by TSIHANG <qh_soledadboy@sina.com>>
 *   1 July, 2017
 *   Personal.Q
 */

#include "oryx.h"
#include "oryx_rbtree.h"
#include "oryx_list.h"
#include "oryx_ipc.h"
#include "oryx_cvhash.h"

#define THRESHOLD_L1(i) (i*0.08)
#define THRESHOLD_L2(i) (i*0.15)
#define THRESHOLD_L3(i) (i*0.20)

/** Input times. */
#define MAX_INJECT_DATA	10000000

/** Physical node number. */
#define MAX_BACKEND_MACHINES	100

/** Physical node definition. */
struct node_t backend_node[MAX_BACKEND_MACHINES] = {
		{"Default0", "127.0.0.1", -1, -1, 0, {NULL, NULL}, 0}
};

/** Record map changes from virtual node to physical node 
	when a physical node added or removed. 
	This variable is always used to check consistency for hash.  */
int changes = 0;


struct chash_root * ch_template;
struct chash_root * ch_add;
struct chash_root * ch_del;


#define TIME_DECLARE()\
	clock_t __s, __e;

#define TIME_START()\
	__s = clock();

#define TIME_FINAL()\
	__e = clock();

#define TIME_CALC()\
	;//printf ("Time occured %f s, %lu, %lu\n", (double) ((__e  - __s)/(double)CLOCKS_PER_SEC), __s, __e);

uint32_t md5_hash (char *instr, size_t s)
{
	int i;
	long hash = 0;
	unsigned char digest[16];
	apr_md5_ctx_t context;

	apr_md5_init(&context);
	apr_md5_update (&context, instr, s);
	apr_md5_final (digest, &context);

	/* use successive 4-bytes from hash as numbers */
	for (i = 0; i < 4; i++) {
	    hash += ((long)(digest[i*4 + 3]&0xFF) << 24)
	        | ((long)(digest[i*4 + 2]&0xFF) << 16)
	        | ((long)(digest[i*4 + 1]&0xFF) <<  8)
	        | ((long)(digest[i*4 + 0]&0xFF));
	}

	return hash;
}

/** Hash function. */
uint32_t hash_algo (char *instr, size_t s)
{
	return md5_hash (instr, s);
	//return oryx_fnv1_hash (instr, s);
}

/** Random value generator. */
static __oryx_always_inline__
uint32_t next_rand_ (uint32_t *p)
{
	uint32_t seed = *p;

	seed = 1103515145 * seed + 12345;
	*p = seed;

	return seed;
}

/** A random IPv4 address generator.*/
void ipaddr_generate (char *ipv4)
{
#define itoa(a,s,t)\
	sprintf (s, "%d", a);

	int a = 0, b = 0, c = 0, d = 0;
	char aa[4], bb[4], cc[4], dd[4];
	
	a = rand () % 256;
	b = rand () % 256;
	c = rand () % 256;
	d = rand () % 256;

	itoa (a, aa, 10);
	itoa (b, bb, 10);
	itoa (c, cc, 10);
	itoa (d, dd, 10);

	strcpy (ipv4, aa);
	strcat (ipv4, ".");
	strcat (ipv4, bb);
	strcat (ipv4, ".");
	strcat (ipv4, cc);
	strcat (ipv4, ".");
	strcat (ipv4, dd);
	
}

void random_string_generate (char *key, size_t s)
{

	int i = 0;
	uint32_t rand = random();
	char *base = "abcdefghijklmnopqrstuvwxyz0123456789";
	
	next_rand_ (&rand);
	
	for (i = 0; i < (int)(s - 1); i ++) {
		int offset = rand % strlen(base);
		key[i] = base[offset];
		next_rand_ (&rand);
	}
}

/** Virtual node comparison handler which used to find a virtual node with a STR key
	in and registered to a RB root. */
static __oryx_always_inline__
int _vn_cmp (const struct rb_node* pos, const void* ptr)
{
    struct vnode_t* vn = rb_entry(pos, struct vnode_t, node);
    return strcmp((char*)ptr, VN_KEY_S(vn));
}

/** Virtual node comparison handler which used to find a virtual node with a ADDR key
	in and registered to a RB root. */
static __oryx_always_inline__
int _vn_cmpp (const struct rb_node* pos, const void* ptr)
{
    struct vnode_t* vn = rb_entry(pos, struct vnode_t, node);
    return ((intptr_t)ptr - VN_KEY_P(vn));
}

/** Virtual node comparison handler which used to find a virtual node with a INTEGER key
	in and registered to a RB root. */
static __oryx_always_inline__
int _vn_cmpi (const struct rb_node* pos, const void* ptr)
{
    struct vnode_t* vn = rb_entry(pos, struct vnode_t, node);
    return (int)(*(uint32_t *)ptr - VN_KEY_I(vn));
}

/** Virtual node dump handler. */
static __oryx_always_inline__
void _vn_dump (struct vnode_t *vn, int __attribute__((__unused__)) flags)
{

	if (unlikely(!vn))
		return;

	struct node_t * n = vn->physical_node;
		
	printf ("-- \"%s(%d)\"@%s(%d vnodes)\n", vn->videsc, vn->index, n->ipaddr, n->replicas);
}

/** Virtual node travel handler which used to travek all virtual node
	and execute $fn. */
static __oryx_always_inline__
void _vn_travel (struct chash_root *ch, void (*fn)(struct vnode_t *, int), int flags)
{
	
	struct rb_node* rbn;
	struct vnode_t* vn;
	
	rbn = rb_first(&ch->vn_root);

	if (flags & NODE_FLG_CLASSFY_TRAVEL) {
		struct node_t *n1 = NULL, *p;
		
		oryx_thread_mutex_lock (&ch->nhlock);
		list_for_each_entry_safe (n1, p, &ch->node_head, node) {
			
			rbn = rb_first (&ch->vn_root);
			while (rbn) {
				vn = rb_entry (rbn, struct vnode_t, node);
				if (likely (vn)) {
					if ((intptr_t)n1 == (intptr_t)vn->physical_node) {
						if (likely (fn))
							fn (vn, flags);
					}
				}
				
				rbn  = rb_next(rbn);
			}
		}
		oryx_thread_mutex_unlock (&ch->nhlock);
		
	}

	else {
		while(rbn) {
			vn = rb_entry(rbn, struct vnode_t, node);
			if (likely (vn)) {
				if (likely (fn))
					fn (vn, flags);
			}
			rbn  = rb_next(rbn);
		}
	}
}

/** Virtual node allocation handler which used to allocating a new virtual node
	and returns its address. */
static __oryx_always_inline__
void *_vn_alloc(void *n, uint32_t key, int i, char *videsc)
{

	struct vnode_t *vn;

	vn = (struct vnode_t *)malloc (sizeof (struct vnode_t));
	if (likely (vn)) {
		
		rb_init_node(&vn->node);
		vn->physical_node = n;
		vn->index = i;
		vn->videsc = malloc (strlen (videsc));
		VN_KEY_I(vn) = key;
		
		if (likely (vn->videsc))
			memcpy (vn->videsc, videsc, strlen (videsc));
	}

	return vn;
}

/** Find a node which key is minimum (or, maximum) among all node. */
static __oryx_always_inline__
struct vnode_t *_vn_default (struct chash_root *ch)
{

	struct vnode_t *dvn = NULL;
	
	VN_DEFAULT(ch, dvn);

	printf ("***    default VN(%s, %u) used !!!\n", dvn->videsc, VN_KEY_I(dvn));
	return dvn;
}

/** Find a node which has a same $KEY. */
static __oryx_always_inline__
void* _vn_find (struct chash_root *ch, const void* key)
{

	struct vnode_t *vn = NULL;
	struct rb_node* pos;

	if(likely(ch) && likely(key) &&
		(NULL != (pos = rb_find (&ch->vn_root, key))))
		vn = rb_entry (pos, struct vnode_t, node);

	return vn;
}

/** Find a node who's key is nearest by $KEY at clockwise. */
static __oryx_always_inline__
void *_vn_find_ring (struct chash_root *ch, const void *key)
{

	int ret;
	struct rb_root *root = &ch->vn_root;
	struct rb_node *node = root->rb_node;
	struct rb_node *rbn = NULL;
	struct vnode_t *vn = NULL;
	
	while (node) {
		ret = root->cmp(node, key);
/**
		if (ret == 0) { return node; }
*/
		if (ret >= 0) { rbn = node; node = node->rb_left; }
		else if (ret < 0) { node = node->rb_right; }
    }

	if (rbn)
		vn = rb_entry (rbn, struct vnode_t, node);
	else
		VN_DEFAULT (ch, vn);
	
        return vn;
}

/** Add a virtual node to a phsical node. */
static __oryx_always_inline__
int _vn_add (struct chash_root *ch, struct node_t *n, struct vnode_t *vn)
{
	if(unlikely(!vn))
	    return -1;

	if (!rb_insert (&vn->node, &ch->vn_root, (void *)(uint32_t *)&VN_KEY_I(vn)))
		n->valid_vns ++;

	 return 0;
}

/** Default naming function for a virtual node. Actually, you can change it if needed.*/
static __oryx_always_inline__
void _vn_fmt (char *idesc_in, int i, char *v_idesc_out, size_t *lo)
{
	*lo = sprintf (v_idesc_out, "%s_%d", idesc_in, i);
}

/** Clone a physical node. */
static __oryx_always_inline__
void * _n_clone (struct node_t *n)
{
	struct node_t *shadow;

	shadow = (struct node_t *)malloc (sizeof (struct node_t));
	if (likely (shadow)) {

		memset (shadow, 0, sizeof (struct node_t));
		
		shadow->flags = 0;
		shadow->replicas = n->replicas;
		strcpy (shadow->ipaddr, n->ipaddr);
		strcpy (shadow->idesc, n->idesc);
		N_HITS(shadow) = 0;
		N_VALID_VNS(shadow) = 0;
		INIT_LIST_HEAD(&shadow->node);
	}

	return shadow;
}

/** New a physical node. */
static __oryx_always_inline__
void * _n_new ()
{
	struct node_t *shadow;
	char key[32];
	
	shadow = (struct node_t *)malloc (sizeof (struct node_t));
	if (likely (shadow)) {

		memset (shadow, 0, sizeof (struct node_t));
		
		shadow->flags = 0;
		shadow->replicas = NODE_DEFAULT_VNS;
		
		ipaddr_generate (key);
		strcpy (shadow->ipaddr, key);

		random_string_generate (key, 32);
		strcpy (shadow->idesc, key);

		N_HITS(shadow) = 0;
		N_VALID_VNS(shadow) = 0;
		INIT_LIST_HEAD(&shadow->node);
	}

	return shadow;
}

/** Add a physical node to list after DBCC. */
static __oryx_always_inline__
int _n_add (struct chash_root *ch, struct node_t *n)
{

	struct node_t *n1 = NULL, *p;

	oryx_thread_mutex_lock (&ch->nhlock);
	
	list_for_each_entry_safe(n1, p, &ch->node_head, node){
		if (!oryx_strcmp_native(n->ipaddr, n1->ipaddr)){
			printf ("A same machine %15s(\"%s\":%p)\n\n", 
						n1->idesc, n1->ipaddr, n1);
			oryx_thread_mutex_unlock (&ch->nhlock);
			return -1;
		}
	}

	list_add_tail (&n->node, &ch->node_head);
	ch->total_ns ++;
	N_HITS(n) = 0;
	N_VALID_VNS(n) = 0;
	
	oryx_thread_mutex_unlock (&ch->nhlock);
	
	return 0;
}

/** Delete a specified physical node from list. */
static __oryx_always_inline__
int _n_del (struct chash_root *ch, struct node_t *n)
{

	list_del (&n->node);
	ch->total_ns --;

	return 0;
}

struct chash_root *chash_init ()
{
	struct chash_root *ch;

	ch = (struct chash_root *) malloc (sizeof (struct chash_root));
	if (unlikely(!ch)) {
		printf ("Can not alloc memory. \n");
		return NULL;
	}

	ch->hash_func = hash_algo;
	rb_init (&ch->vn_root, _vn_cmpi);
	INIT_LIST_HEAD (&ch->node_head);

	return ch;
}

/** Caculate total virtual node counter. */
int total_vns (struct chash_root *ch)
{
	int vns=0;
	struct node_t *n1 = NULL, *p;
	
	oryx_thread_mutex_lock (&ch->nhlock);
	
	list_for_each_entry_safe(n1, p, &ch->node_head, node)
		vns += n1->valid_vns;
	
	oryx_thread_mutex_unlock (&ch->nhlock);

	return vns;
}

/** Remove a specified physical node from list.
	Erase all its virtual node and update gloable default virtual node. */
struct node_t *node_remove (struct chash_root *ch, char *nodekey)
{
	int i;
	uint32_t hv;
	size_t lo = 0;
	char key[32] = {0};
	struct node_t *n = NULL, *n1 = NULL, *p;
	struct vnode_t *vn = NULL;

	/* Find the physical node by $nodekey  */
	oryx_thread_mutex_lock (&ch->nhlock);
	
	list_for_each_entry_safe(n1, p, &ch->node_head, node) {
		if (!oryx_strcmp_native(n1->ipaddr, nodekey)){
			oryx_thread_mutex_unlock (&ch->nhlock);
			n = n1;
			goto find;
		}
	}
	
	oryx_thread_mutex_unlock (&ch->nhlock);
	return NULL;
	
find:

	for (i = 0; i < n->replicas; i ++) {
		
		_vn_fmt (n->ipaddr, i, key, &lo);
	
		hv = ch->hash_func (key, strlen (key));
		vn = _vn_find (ch, (void *)&hv);
		if (!vn) continue;
		{
			n1 = vn->physical_node;
			rb_erase (&vn->node, &ch->vn_root);
			n1->valid_vns --;
		}
	}

	_n_del (ch, n);

	ch->vn_max = NULL;
	ch->vn_min = NULL;
	
	oryx_thread_mutex_lock (&ch->nhlock);
	
	list_for_each_entry_safe(n1, p, &ch->node_head, node) {
		
		for (i = 0; i < n1->replicas; i ++) {
			_vn_fmt (n1->ipaddr, i, key, &lo);
			hv = ch->hash_func (key, strlen (key));
			vn = _vn_find (ch, (void *)&hv);
			if (!vn) continue;

			/** Init the maximun and minmum (of key) node */
			if (ch->vn_max == NULL)
				ch->vn_max = &vn->node;
			if (ch->vn_min == NULL)
				ch->vn_min = &vn->node;
			
			/** Update the maximun (of key) node */
			if (ch->vn_max != NULL) {
				struct vnode_t *vn_max = rb_entry(ch->vn_max, struct vnode_t, node);
				if (VN_KEY_I(vn_max) < VN_KEY_I(vn))
					ch->vn_max = &vn->node;
			}

			/** Update the minimun (of key) node */
			if (ch->vn_min != NULL) {
				struct vnode_t *vn_min = rb_entry(ch->vn_min, struct vnode_t, node);
				if (VN_KEY_I(vn_min) > VN_KEY_I(vn))
					ch->vn_min = &vn->node;
			}
		
		}
	}
	
	oryx_thread_mutex_unlock (&ch->nhlock);

	return n;
}

/** Install a specified physical node to list. */
void node_install (struct chash_root *ch, struct node_t *n)
{

	int i;
	size_t lo = 0;
	uint32_t hv = 0;
	struct vnode_t *vn;
	char v_idesc [32] = {0};

	if (_n_add (ch, n)) {
		printf ("%15s(%15s) has installed \n", n->idesc, n->ipaddr);
		return;
	}
	
	for (i = 0; i < n->replicas; i++) {

		memset (v_idesc, 0, 32);
		lo = 0;
		
		_vn_fmt (n->ipaddr, i, v_idesc, &lo);
		hv = ch->hash_func (v_idesc, lo);
		
		vn = _vn_find (ch, (void *)(uint32_t *)&hv);
		if (likely (vn)) {
			printf ("%s_%u(%s) has added \n", v_idesc, VN_KEY_I(vn), n->ipaddr);
			return;
		}
		
		/* Allocate a VN and inited VN with $hv and node */
		vn = _vn_alloc (n, hv, i, v_idesc);
		if (unlikely (!vn)) {
			printf ("Can not alloc memory for %s\n", v_idesc);
			return;
		}

		if (!_vn_add (ch, n, vn)) {

			/** Init the maximun and minmum (of key) node */
			if (ch->vn_max == NULL)
				ch->vn_max = &vn->node;
			if (ch->vn_min == NULL)
				ch->vn_min = &vn->node;
			
			/** Update the maximun (of key) node */
			if (ch->vn_max != NULL) {
				struct vnode_t *vn_max = rb_entry(ch->vn_max, struct vnode_t, node);
				if (VN_KEY_I(vn_max) < VN_KEY_I(vn))
					ch->vn_max = &vn->node;
			}

			/** Update the minimun (of key) node */
			if (ch->vn_min != NULL) {
				struct vnode_t *vn_min = rb_entry(ch->vn_min, struct vnode_t, node);
				if (VN_KEY_I(vn_min) > VN_KEY_I(vn))
					ch->vn_min = &vn->node;
			}
		}
	}

}

/** Lookup a physical node from list with a specified key. */
struct node_t *node_lookup (struct chash_root *ch, char *key)
{
	uint32_t hv;
	struct vnode_t *vn = NULL;
	struct node_t *n = _vn_default(ch)->physical_node;

	hv = ch->hash_func (key, strlen (key));
	
	vn = _vn_find_ring(ch, (void *)(uint32_t *)&hv);
	if (likely(vn))
		n = vn->physical_node;
	else
		printf ("Can not find vn with a (%s, %u)\n", key, hv);
	
	ch->total_hit_times ++;
	N_HITS_INC(n);
	
	return n;
}

/** Dump all physical node and statistics.*/
void node_summary (struct chash_root *ch)
{
	struct node_t *n1 = NULL, *p;

	printf ("\n\n\nTotal %15d(%-5d vns) machines\n", ch->total_ns, total_vns(ch));

	printf ("%15s%16s%4s%15s%15s\n", "MACHINE", "IPADDR", "VNS", "HIT", "RATIO");
	oryx_thread_mutex_lock (&ch->nhlock);
	
	list_for_each_entry_safe(n1, p, &ch->node_head, node){
		printf ("%15s%16s%4d%15d%15.2f%s\n", 
					n1->idesc, n1->ipaddr, n1->valid_vns, N_HITS(n1), (float)N_HITS(n1)/ch->total_hit_times * 100, "%");
	}

	oryx_thread_mutex_unlock (&ch->nhlock);
}

/** Dump all physical node.*/
void node_dump (struct chash_root *ch)
{
	printf ("\n\n===========Virtual Nodes (%d)============\n", total_vns(ch));
	_vn_travel (ch, _vn_dump, NODE_FLG_CLASSFY_TRAVEL);
}

/** Physical node configuration.*/
void node_set (struct node_t *n, char *desc, char *ipaddr, int replicas)
{
	memcpy ((void *)&n->idesc[0], desc, strlen(desc));
	memcpy ((void *)&n->ipaddr[0], ipaddr, strlen(ipaddr));
	n->flags = NODE_FLG_INITED;
	n->replicas = replicas;
	INIT_LIST_HEAD (&n->node);
}

void chcopy (struct chash_root **new, struct chash_root *old)
{

	struct chash_root *backup;
	struct node_t *n1 = NULL, *p;

	backup = chash_init ();
	
	list_for_each_entry_safe(n1, p, &old->node_head, node){
		struct node_t *shadow;
		shadow = _n_clone (n1);
		node_install (backup, shadow);
	}

	*new = backup;
}

void check_miss_while_add ()
{

	int i;
	uint32_t hv;
	uint32_t intp = 0;
	char key[32] = {0};
	struct chash_root *chnew = NULL, *ch = NULL;
	char *colur = CONSOLE_PRINT_CLOR_LWHITE;
	struct node_t *n = NULL, *new = NULL;
	struct vnode_t *vn = NULL, *vn_backup = NULL;

	chnew = ch_add;
	chcopy (&ch, chnew);
	
	changes = 0;
	
	new = _n_new ();
	if (likely (new)) {
		node_install (ch, new);
		printf ("\n\n\n\nTrying to add a node ... \"%s\", done, total_vns=%d\n", 
			new->ipaddr, total_vns(ch));
	}

	for (i = 0; i < MAX_INJECT_DATA; i ++) {
		memset ((void *)&key[0], 0, 32);
		sprintf (key, "2.%d.%d.%d", 
			((i * next_rand_(&intp)) % 255),
			((i * next_rand_(&intp)) % 255),
			((i * next_rand_(&intp)) % 255));

		hv = ch->hash_func (key, strlen (key));
		
		vn = _vn_find_ring(ch, (void *)(uint32_t *)&hv);
		if (likely(vn))
			n = vn->physical_node;
		
		if (likely(n)) {
			ch->total_hit_times ++;
			N_HITS_INC(n);
			//printf ("[%16s] is in node: [%16s]\n", key, n->idesc);
		}
		
		vn_backup = _vn_find_ring (chnew, (void *)(uint32_t *)&hv);
		vn = _vn_find_ring(ch, (void *)(uint32_t *)&hv);

		if (oryx_strcmp_native (
				((struct node_t *)vn->physical_node)->idesc, 
				((struct node_t *)vn_backup->physical_node)->idesc)) 
			changes ++;
		
	};

	if (changes <= THRESHOLD_L1(MAX_INJECT_DATA))
		colur = CONSOLE_PRINT_CLOR_LWHITE;
	
	if ((changes > THRESHOLD_L1(MAX_INJECT_DATA)) && (changes <= THRESHOLD_L2(MAX_INJECT_DATA)))
		colur = CONSOLE_PRINT_CLOR_LYELLOW;

	if (changes >= THRESHOLD_L2(MAX_INJECT_DATA))
		colur = CONSOLE_PRINT_CLOR_LRED;
	
	printf ("\nAdding ...%18s (%s)\n Changes (%-8u%s%-4.2f%s"CONSOLE_PRINT_CLOR_FIN")\n\n", 
		new->ipaddr, new->idesc, 
		changes, colur, (float)changes/MAX_INJECT_DATA * 100, "%");

}

void check_miss_while_rm ()
{

	int i;
	uint32_t hv;
	uint32_t intp = 0;
	char key[32] = {0};
	struct chash_root *chnew = NULL, *ch = NULL;
	char *colur = CONSOLE_PRINT_CLOR_LWHITE;
	struct node_t *n = NULL;
	struct vnode_t *vn = NULL, *vn_backup = NULL;
	struct node_t *removed_node = &backend_node[1];

	chnew = ch_del;
	chcopy (&ch, chnew);
	
	changes = 0;
	
	n = node_remove (ch, removed_node->ipaddr);

	printf ("\n\n\n\nTrying to remove a node ... \"%s\", done, total_vns=%d\n", 
		n->idesc, total_vns(ch));

	free (n);
	
	for (i = 0; i < MAX_INJECT_DATA; i ++) {
		memset ((void *)&key[0], 0, 32);
		sprintf (key, "2.%d.%d.%d", 
			((i * next_rand_(&intp)) % 255),
			((i * next_rand_(&intp)) % 255),
			((i * next_rand_(&intp)) % 255));

		hv = ch->hash_func (key, strlen (key));
		
		vn = _vn_find_ring(ch, (void *)(uint32_t *)&hv);
		if (likely(vn))
			n = vn->physical_node;
		
		if (likely(n)) {
			ch->total_hit_times ++;
			N_HITS_INC(n);
			//printf ("[%16s] is in node: [%16s]\n", key, n->idesc);
		}
		
		vn_backup = _vn_find_ring (chnew, (void *)(uint32_t *)&hv);
		vn = _vn_find_ring(ch, (void *)(uint32_t *)&hv);

		if (oryx_strcmp_native (
				((struct node_t *)vn->physical_node)->idesc, 
				((struct node_t *)vn_backup->physical_node)->idesc)) 
			changes ++;
		
	};

	if (changes <= THRESHOLD_L1(MAX_INJECT_DATA))
		colur = CONSOLE_PRINT_CLOR_LWHITE;

	if ((changes > THRESHOLD_L1(MAX_INJECT_DATA)) && (changes <= THRESHOLD_L2(MAX_INJECT_DATA)))
		colur = CONSOLE_PRINT_CLOR_LYELLOW;
	
	if (changes >= THRESHOLD_L2(MAX_INJECT_DATA))
		colur = CONSOLE_PRINT_CLOR_LRED;
	
	printf ("\nRemoving ...%18s (%s)\n Changes (%-8u%s%-4.2f%s"CONSOLE_PRINT_CLOR_FIN")\n\n", 
		removed_node->ipaddr, removed_node->idesc, 
		changes, colur, (float)changes/MAX_INJECT_DATA * 100, "%");

}

/** A test handler.*/
void lookup_handler ()
{

	int i = 0;
	uint32_t hv;
	uint32_t intp = 0;
	char key[32] = {0};
	struct node_t *n = NULL;
	struct vnode_t *vn = NULL;
	struct chash_root *ch = ch_template;
	
	chcopy (&ch_add, ch);
	chcopy (&ch_del, ch);
	
	printf ("\n\n\nTrying to inject %d object to %d nodes ... (please wait for a while)\n", 
		MAX_INJECT_DATA, MAX_BACKEND_MACHINES);
	
	FOREVER {

		for (i = 0; i < MAX_INJECT_DATA; i ++) {
			memset ((void *)&key[0], 0, 32);
			sprintf (key, "2.%d.%d.%d", 
				((i * next_rand_(&intp)) % 255),
				((i * next_rand_(&intp)) % 255),
				((i * next_rand_(&intp)) % 255));

			hv = ch->hash_func (key, strlen (key));

			vn = _vn_find_ring(ch, (void *)(uint32_t *)&hv);
			if (likely(vn))
				n = vn->physical_node;
			
			if (likely(n)) {
				ch->total_hit_times ++;
				N_HITS_INC(n);
				//printf ("[%16s] is in node: [%16s]\n", key, n->idesc);
			}
		};

		node_summary (ch);

		check_miss_while_rm ();
		check_miss_while_add ();
		
		break;
	};
	
}

int main ()
{

	int i = 0;

	ch_template = chash_init();
	
	for (i = 0; i < MAX_BACKEND_MACHINES; i++) {
		char key [32];
		char machine[32];
		sprintf (machine, "Machine_%d", i);
		ipaddr_generate (key);
		node_set (&backend_node[i], machine, key, 160);
	}

	for (i = 0; i < MAX_BACKEND_MACHINES; i ++) {
		struct node_t *shadow;
		shadow = _n_clone (&backend_node[i]);
		node_install (ch_template, shadow);
	}
	
	lookup_handler ();

	return 0;
}

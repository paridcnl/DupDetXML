/*************
encode-pre-post.c
Encodes a given tree into a sequence of nodes. 
Start tag of a node is encoded in pre-order.
Content (i.e. attributes, values, etc.) are also encoded in pre-order.
End tag of a node is encoded in post-order.
*/
/*************
encode-rootpath8.c
...
...
encode-rootpath.c
Encodes root path
*/

/**************
encode-nest.c
Encodes based on NEST scheme (Efficient and Scal... paper, Tsotras, 2009, WebDB)
*/

/*****************************************************************
 * outline.c
 */


//#include <sys/types.h>
#include <time.h>

#include <stdio.h>
#include <expat.h>
#include <string.h>
#include <math.h>

//#include "encode-rootpath.h"
#include "inputfile.h"
#include "structdef.h"
#include "structures.h"
#include "b.h"

#include "EditDistance.c"
#include "SplitStr.c"

//#include "print.c"

#if defined(__amigaos__) && defined(__USE_INLINE__)
#include <proto/expat.h>
#endif

#ifdef XML_LARGE_SIZE
#if defined(XML_USE_MSC_EXTENSIONS) && _MSC_VER < 1400
#define XML_FMT_INT_MOD "I64"
#else
#define XML_FMT_INT_MOD "ll"
#endif
#else
#define XML_FMT_INT_MOD "l"
#endif

#define BUFFSIZE        8192
//#define BUFFSIZE        256

#define DEBUG 0

char Buff[BUFFSIZE];
int Depth;

//default values
#define MAX_CONTENTID 2000
#define TABLE_SZ_SW 27 /*size of stop word list*/

#define BENCH 1
//#define BENCH 2
//#define BENCH 3

//'Cora.xml' dataset
#if BENCH == 1
//#define NUM_DOCS 1879
#define NUM_DOCS 1879*2
#endif

//'FreeDB.xml' dataset (cddb)
#if BENCH == 2
#define NUM_DOCS 9764
//#define NUM_DOCS 17533
//#define MAX_CONTENTID 4000
#define MAX_CONTENTID 1000
#define TABLE_SZ_SW 28 /*size of stop word list*/
#endif

//'CountryDB.xml' dataset
#if BENCH == 3
#define NUM_DOCS 260
#define NUM_DOCS 260*2
#define MAX_CONTENTID 4000
#endif

//#define TABLE_SZ MAX_NUM_TAGS /*size of tag ID table*/

#define MAX_NUM_TAGS 25 /*max num of tags in dataset*/
#define TABLE_SZ MAX_NUM_TAGS /*size of tag ID table*/

//#define TABLE_SZ_SW 20 /*size of stop word list*/
//#define TABLE_SZ_SW 27 /*size of stop word list*/

typedef struct t_ent
{
const char element_ptr[MAX_ELE_SZ];
short id;
}tag_ent;

//static 
int tag_id_table[TABLE_SZ];
//static 
const char tag_table[TABLE_SZ][MAX_ELE_SZ+1];
//static 
const char stop_word_table[TABLE_SZ_SW][MAX_ELE_SZ+1];
//static int stop_word_table[TABLE_SZ_SW];

//#define MAX_CONTENTID 2000
#define THETA1 7
#define THETA_STR 0.5

//#define STR_SIM_THRESH 0.8
#define STR_SIM_THRESH 1.0
//#define STR_SIM_THRESH 0.7
//#define STR_SIM_THRESH 0.9

//#define CAND_SIM_THRESH 0.3
#define CAND_SIM_THRESH 0.7
//#define CAND_SIM_THRESH 0.8
//#define CAND_SIM_THRESH 0.9
//#define CAND_SIM_THRESH 1.0

//#define MAX_NUM_DOCS 64000
#define MAX_NUM_DOCS NUM_DOCS

#define ELE_SIM_THRESH 0.5
#define STACK_SIM_THRESH 0.5
#define FINAL_SIM_THRESH 0.5
#define FINAL_SIM_THRESH 0.7
#define DUP_SIM_THRESH FINAL_SIM_THRESH

#define MIN_DF	1 
//#define MIN_DF	0 
//#define MAX_DF 10
#define MAX_DF 100
//#define MAX_DF 500

//static int tag_id_table_term[TABLE_SZ][MAX_CONTENTID];
int tag_id_table_term[TABLE_SZ][MAX_CONTENTID];
//static const char tag_table_term[TABLE_SZ][MAX_CONTENTID][MAX_CONTENT_SZ];
const char tag_table_term[TABLE_SZ][MAX_CONTENTID][MAX_CONTENT_SZ];

//static 
int tag_id_table_count[TABLE_SZ][MAX_CONTENTID];

//static 
float idf[TABLE_SZ][MAX_CONTENTID];

typedef struct t_node
{
int type;
short tag_id;
}node_ent;

static short tag_table_ptr;
static int curr_node_ptr;
static int tag_found_flag;

static char error_msg[80];

/*End:NEST declarations, data structures*/

/*Start:rootpath data structures*/
//#define MAX_TREE_DEPTH 8 /*for dblp*/
//#define MAX_TREE_DEPTH 16 /*for general*/
#define MAX_TREE_DEPTH 32 /*for general*/
#define MAX_TOP_STACK MAX_TREE_DEPTH

//stack for tracking root path
static doc_ent1 stack_rp[MAX_TREE_DEPTH];

static int curr_stack_ptr = -1;

//static stack_ent rp_nodelist[MAX_INPUT_SZ];
short rp_nodelist[MAX_INPUT_SZ];

doc_metadata document[MAX_NUM_DOCS];

static int curr_rp_node_ptr = 0;
int pre_order_trav_number;

static short last_tag_pushed = 0;

static doc_ent doc_list[MAX_NUM_DOCS];

static int tag_table_count[TABLE_SZ] = {0};
static doc_ent_sel doc_list_sel[MAX_NUM_DOCS];

//static doc_ent_sel doc_list_sel1[MAX_NUM_DOCS];

static cand_set_ent cand_set_list[MAX_NUM_DOCS];
static cand_set_ent duplicate_set_list[MAX_NUM_DOCS];

//static bool duplicate_matrix[2000][2000];
static bool duplicate_matrix[NUM_DOCS][NUM_DOCS];

/*End:rootpath data structures*/

/*Start: data structures for partial execution*/

static XML_Parser p;

//static 
int old_rp_nodelist_tag_id; 
//static 
int old_rp_nodelist_n_degree;

//static 
int old_stack_rp_tag_id;
//static 
int old_stack_rp_n_degree;
//static 
short old_last_tag_pushed;
//static 
int old_curr_stack_ptr;
//static 
int old_curr_rp_node_ptr;

//static 
//MyMat tag_index_matrix[MAX_NUM_TAGS];
MyMat tag_index_matrix[1];
//static 
int tag_id_ctr[MAX_NUM_TAGS];

/*End: data structures for partial execution*/

static int exit_fn_flag = 0;

//static 
//stack_ent query_array[QUERY_ARRAY_SZ];
stack_ent query_array[1];

int * tag_index_array;
int tag_index_array_offset[MAX_NUM_TAGS];

void gpu_filter_fn(void);
int data_packing(void);
//int BENCH;
void print_term_freq();
static void print_doc_list_sel(void);
void print_pre_post_tree_seq(void);
void find_duplicates_pre_post_tree_seq(void);

//static char *last_content;
char *last_content;

//static int last_tag = 0;
short last_tag = 0;
static int document_count = 0;
static int document_count_plus = 0;

static int num_string_comparisons1 = 0;
static int num_string_comparisons2 = 0;

int content_len = 0;
//#include "print.c"

static void
print_params(void)
{
	printf("\nMAX_ELE_SZ=%d", MAX_ELE_SZ);
	printf("\nMAX_CONTENT_SZ=%d", MAX_CONTENT_SZ);
	printf("\nprinting parameters:\n");

	printf("\nMAX_CONTENTID = %d", MAX_CONTENTID );

	printf("\nMIN_DF = %d", MIN_DF );
	printf("\nMAX_DF = %d", MAX_DF );

	//printf("\nTHETA1 = %1.2f", THETA1 ); 
	//printf("\nTHETA_STR = %1.2f", THETA_STR); 
	printf("\nSTR_SIM_THRESH = %1.2f", STR_SIM_THRESH);
	printf("\nCAND_SIM_THRESH = %1.2f", CAND_SIM_THRESH);
	printf("\nDUP_SIM_THRESH = %1.2f", DUP_SIM_THRESH);

	return;
}

static void 
exit_fn(int error)
{
	fprintf(stdout, "\nexit_fn(): FIX THIS");
	fprintf(stdout, "\noverriding, directing to main()\n");
	exit_fn_flag = 1;
	return;
}

static void print_tag_table()
{

/*
	fprintf(stdout, "\nprint_tag_table , returning, FIX THIS");
	fprintf(stdout, "\ncalling exit_fn()");
	exit_fn(0);
return;

	FILE * f1=fopen("tag_table.txt", "w");
	if (!f1){fprintf(stdout, "\nfile open error..exiting");
		//exit(-1);
		exit_fn(-1);
	}
*/
	short i; int k;
	 	 
	for (i=0; i < TABLE_SZ/*tag_table_ptr*/; i++)
	{
		printf("\ntag=%s", tag_table[i] );
		printf("\ttag_id=%d", tag_id_table[i] );			
	}

	//fclose(f1);
}

static void read_tag_table()
{
        FILE * f2;

	if ( BENCH == 1 )
	{	
        	f2=fopen("tag_cora.txt", "r");
		//printf("\ntag_cora.txt opened");
	}

        if ( BENCH == 2 )
        {
                f2=fopen("tag_FreeDB.txt", "r");
                //printf("\ntag_cora.txt opened");
        }
	
        if ( BENCH == 3 )
        {
                f2=fopen("tag_countryDB.txt", "r");
                //printf("\ntag_cora.txt opened");
        }


//        if (!f2){ fprintf(stderr, "\n'tag_dblp.txt' missing file open error..exiting");
//        if (!f2){ fputs("\n'tag_dblp.txt' missing file open error..exiting", stdout);
        if (!f2){ fputs("f error", stdout);
                //exit(0);
                exit_fn(0);
        }
        
        int t1;

	/*
	//	printf("\nread tag table():");
	if (DEBUG){	fputs("\nread tag table(): returning", stdout);	fputs("\n", stdout);
	}
	*/

        char temp[TABLE_SZ][MAX_ELE_SZ+1];
        const char t_str[MAX_ELE_SZ+1];
        short t_tag;
        int len=0;
        short i; int k;

        char charbuf[16] = {0}; 

        for (i=0;i<TABLE_SZ;i++)
        {
		strcpy(temp[i], "" );
	        tag_id_table[i]=0;
        }

        i = 0;
        int j = 0;

        while ( !feof(f2) )
        {
                fscanf(f2,"%s", t_str );

		{
			/*
			fputs( t_str, stdout ); 	
			*/
	                strcpy( tag_table[j], t_str );
        	        fscanf(f2,"%d", &t_tag );

			int len = sizeof(t_str);
        	        tag_id_table[j] = t_tag;
	
        	        j++;
		}
        }
        fclose(f2);

	//print_tag_table();
	//exit(0);


}

static void read_stop_word_table()
{
        FILE * f2;

         if ( BENCH == 3 )
        {
                f2=fopen("stop_word_tag_cora.txt", "r");
                //printf("\nstop_word_tag_cora.txt opened");
        }

        if ( BENCH == 1 )
        {
                f2=fopen("stop_word_tag_cora.txt", "r");
                //printf("\nstop_word_tag_cora.txt opened");
        }

         if ( BENCH == 2  )
        {
                f2=fopen("stop_word_tag_cddb.txt", "r");
                //printf("\nstop_word_tag_cora.txt opened");
        }


        if (!f2){ fputs("f error", stdout);
                exit_fn(0);
        }

        int t1;

        //char temp[TABLE_SZ][MAX_ELE_SZ+1];
        const char t_str[MAX_ELE_SZ+1];
        short t_tag;
        int len=0;
        short i; int k;

        char charbuf[16] = {0};
	
	//init stop_word_table
        for (i=0;i<TABLE_SZ_SW;i++)
        {
		strcpy( stop_word_table[i], "" );        
		//stop_word_table[i]=0;
        }

        i=0;
        int j=0;

        while ( !feof(f2) )
        {

                fscanf(f2,"%s", t_str );
                {
                strcpy( stop_word_table[j], t_str );
                fscanf(f2,"%d", &t_tag );

                int len = sizeof(t_str);
                //stop_word_table[j] = t_tag;

                j++;
                }
        }
        fclose(f2);
	//append "Various Artist"
	//append "Various ArtistS"
	
	if ( BENCH == 2 )
	{
		strcpy( stop_word_table[j], "Various Artists" );
		j++;
		strcpy( stop_word_table[j], "Various Artist" );
		j++;

	}
	/*	
	for ( i=0; i < TABLE_SZ_SW; i++ )
	printf("\ni=%d\tword = %s", i, stop_word_table[i] );

	exit(0);
	*/
}              

int stderr_exception_handler( char * msg, int len, char * f_name )
{ 

	//fprintf(stdout, "\nstderr_exception_handler - Illegal:");
	exception_handler( msg, len, f_name );
/*
	fprintf(stderr, "\nIllegal:");
	fprintf(stderr, "\nFunction: %s,", f_name);
	fprintf(stderr, "\tError: %s", msg);
	fprintf(stderr, "\tELEMENT length=%d", len);
	fprintf(stderr, "\ncheck  file\tExiting..." );
	//printf("\nPrinting tag table");	 
	//print_tag_table();
	fprintf(stderr, "\ncurr_rp_node_ptr=%d", curr_rp_node_ptr);
	fprintf(stderr, "\nMAX_INPUT_SZ:%d", MAX_INPUT_SZ );

	fprintf(stderr, "\n");
	//exit(0); 
*/
}

int exception_handler( char * msg, int len, char * f_name )
{ 

	fprintf(stdout, "\nIn exception_handler");

	fprintf(stdout, "\nIllegal:");
	fprintf(stdout,"\nFunction: %s,", f_name);
	fprintf(stdout,"\tError: %s", msg);
	fprintf(stdout,"\tELEMENT length=%d", len);
	fprintf(stdout,"\nExiting..." );
	fprintf(stdout,"\nPrinting tag table");	 
	/*print_tag_table();*/
	fprintf(stdout,"\n");
	/*stderr_exception_handler( msg, len, f_name );*/

	exit(0); 
}

/*search or insert*/
static short SEARCH( char *el, int op_type/*'1':start, '0': end*/ )
{
	int i;
	int j;
	int t_tag = -1;
	int diff = 0;
	int len=0;
        const char t_str[MAX_ELE_SZ+1];

                for (j=0; j < TABLE_SZ ; j++)
                {
           		diff = strcmp( el, tag_table[j]);
                        if ( diff == 0 )
                        {
                        	t_tag = tag_id_table[j];
                        	return t_tag;
			}
                }

                /*check overflow*/
                if ( tag_table_ptr >= TABLE_SZ)
                {
                	error_msg[80]="tag not found: tag table overflow";
                	exception_handler("tag not found: tag table overflow", 0, "SEARCH" );
                }

		//not found, so insert
		//if ( op_type == 0 )
		{	printf("\nmissing tag=%s", el );
                	exception_handler("tag missing on POP operation", 0 ,"SEARCH" );
		}

        	return t_tag;
}

//static short SEARCH_term( char *el, short last_tag )
short SEARCH_term( char *el, short last_tag )
{
        int i;
        int j;
        int t_tag_term = -1;
        int diff = 0;
        int len = 0;
        const char t_str[MAX_ELE_SZ+1];

		i = last_tag;
		int len1 = 0;

		if ( !strcmp(el, "Anatoliki Makedhonia kai Thrak" ))
			printf("\n ************** el=%s", el);

                for (j=0; j < tag_table_count[i]; j++)
                {
                        //diff = strcmp( el, tag_table_term[i][j] );
			//len1 = strlen( tag_table_term[i][j] );
			//len1 = len1 - 3 ;

                        diff = strcasecmp( el, tag_table_term[i][j] );
                        //diff = strncasecmp( tag_table_term[i][j], el, len1 );

                        if ( diff == 0 )
                        {
                                t_tag_term = tag_id_table_term[i][j];
                                return t_tag_term;
                        }
                }

                //not found, so insert
                if ( last_tag >= 0 )
                {	
			/*
			if ( document_count < 3 ) {
                                printf("\n last_tag=%d \t el=%s", last_tag, el);
                                //exit(0);
                        }
			
			if ( document_count > 259 ) {
			//if ( document_count < 259 + 10 ) {
				printf("\n last_tag=%d \t el=%s", last_tag, el);
				//exit(0);
			}
			*/
			/*
			if ( document_count > 259 ) { 
				printf("\n last_tag=%d \t el=%s \t content_len=%d", last_tag, el, content_len );
				exit(0);
			}
			*/

			if ( tag_table_count[i] < MAX_CONTENTID )
			{
			j = tag_table_count[i];
			
			strcpy( tag_table_term[i][j], el );
			tag_id_table_term[i][j] = j;
			( tag_table_count[i] )++;	 
               		t_tag_term = j; 

		        return t_tag_term;

			}
		}
}

static short SEARCH_stop_word( char *el )
{
        int i;
        int j;
        int t_tag_term = 0;
        int diff = 0;
        int len = 0;
        const char t_str[MAX_ELE_SZ+1];

                i = last_tag;

                for (j=0; j < TABLE_SZ_SW; j++)
                {
                        diff = strcasecmp( el, stop_word_table[j] );

                        if ( diff == 0 )
                        {
                                t_tag_term = 1;// ag_id_table_term[i][j];
	
				//printf("\nSAERCH: stop word = %s\tj= %d \t word = %s", el, j, stop_word_table[j]  );
                                return t_tag_term;
	
                        }
                }

	return t_tag_term;
}

static void 
print_stack()
{
	int i;

	fprintf(stdout, "\nStack:curr_stack_ptr=%d",curr_stack_ptr);
	for (i=0; i < MAX_TOP_STACK/*curr_stack_ptr*/; i++)
	{
		//printf("\nstack:i=%d\t%d\t%d\t%s", i, stack_rp[i].tag_id, stack_rp[i].n_degree, stack_rp[i].el );
		fprintf(stdout, "\nstack:i=%d\t%d\t%d", i, stack_rp[i].tag_id, stack_rp[i].n_degree  );
	}
		fprintf(stdout, "\n");	
}

//static int t_curr_stack_ptr = -1;

static void 
push_stack(int tag, const char * el, const char **attr )
{
	int i;

	curr_stack_ptr++;
	last_tag_pushed = stack_rp[curr_stack_ptr].tag_id = tag;

	return;
}

static void 
pop_stack()
{
	char zero_str[20]="";

	stack_rp[curr_stack_ptr].tag_id = 0;
	strcpy(stack_rp[curr_stack_ptr].attr, zero_str );
	strcpy(stack_rp[curr_stack_ptr].content, zero_str );

	stack_rp[curr_stack_ptr].content_id = 0;

	curr_stack_ptr--;

	return;
}

static int stop_word_count = 0;

static void 
encode_node_rp(void)
{
	int i;
	int stop_word = 0;

	//sanity check
	if ( curr_stack_ptr > MAX_TOP_STACK )
	{ 
		strcpy( error_msg, "curr_stack_ptr > MAX_TOP_STACK"); 	
		printf("\ncurr_stack_ptr=%d\tcurr_rp_node_ptr=%d\tMAX_INPUT_SZ=%d\tstack_count=%s", curr_stack_ptr, curr_rp_node_ptr, MAX_INPUT_SZ,  doc_list[document_count].stack_count );
		exception_handler( error_msg, curr_stack_ptr, "encode_node_rp" );
	}

	if ( curr_rp_node_ptr >= MAX_INPUT_SZ )
	{ 
		strcpy( error_msg, "curr_rp_node_ptr >= MAX_INPUT_SZ"); 
		fprintf(stdout," curr_rp_node_ptr=%d\tMAX_INPUT_SZ=%d", curr_rp_node_ptr, MAX_INPUT_SZ );
		exception_handler( error_msg, 0, "encode_node_rp" );
	} 
	/*
	//check 'stack_count'
	if ( doc_list[document_count].stack_count >= MAX_STACKS )
	{
		//return;	//no more encoding of 'stacks' (or rootpaths) for this object.
		printf("\nencode_rp_node():docuemnt_count=%d\tstack_count=%d\tnot exiting...",document_count, doc_list[document_count].stack_count );
		//exit(0);
	} 
	*/
	int cnt = 0;//( doc_list[document_count].stack_count )++;	

	//sanity check	
	//if ( cnt < MAX_STACKS )
	if ( doc_list[document_count].stack_count < MAX_STACKS )
	{

		cnt = doc_list[document_count].stack_count;
	
		doc_list[document_count].stack_size[cnt] = curr_stack_ptr;
	
		//add content of stack (from bottom '0'th position to top )
		for (i=0; i <= curr_stack_ptr; i++)
		{
			//Add string splitter part here:	

			//skip if entry is a 'stop word'
			stop_word = 0;

			if ( stack_rp[i].content != NULL )
			{

			stop_word = SEARCH_stop_word( stack_rp[i].content );		

			if ( stop_word > 0 ) 
			{
				stop_word_count++; 
				//printf("\nstop word = %s",  stack_rp[i].content );
				continue;
			}
			}

        		doc_list[document_count].tag_id[cnt][i] = stack_rp[i].tag_id;

	        	strcpy( doc_list[document_count].attr[cnt][i], stack_rp[i].attr );
        		strcpy( doc_list[document_count].content[cnt][i], stack_rp[i].content );
			doc_list[document_count].content_id[cnt][i] = stack_rp[i].content_id;
		}

		//now increment 'stack_count'
		( doc_list[document_count].stack_count )++;
	}

	return;
}

static void 
update_node_degree(void)
{
	return;

	//for every node is POPed off stack, update degree of parent node
	( stack_rp[curr_stack_ptr].n_degree )++;
	return;
}

static void 
print_rp_nodes()
{
	int i, j, z;
	int max_stack_count = 0;
	int max_docid = 0;

	printf("\nprint_doc_list:");

	for (i=0; i <= /*MAX_INPUT_SZ*/ document_count; i++)
	{
		printf("\ndocid=%d\tstack_count=%d", i, doc_list[i].stack_count );

		if ( doc_list[i].stack_count >= MAX_STACKS )
		{	printf("\nprint_rp_node():max stack error, not exiting...resetting to '0'");	
			//FIX THIS:
			doc_list[i].stack_count = 0;
		}

                if ( doc_list[i].stack_count > max_stack_count )
		{
			max_stack_count = doc_list[i].stack_count;
			max_docid = i; 
		}
	/*
	for (j=0; j < doc_list[i].stack_count; j++)
	{	printf("\nstack_count=%d", j );
		for (z=0; z <= doc_list[i].stack_size[j]; z++)
		{
			printf("\nstack_size=%d", doc_list[i].stack_size[j] );
			printf("\ti=%d\tj=%d\ttag_id=%d", i, j, doc_list[i].tag_id[j][z] ); 
			printf("\tattr=%s", doc_list[i].attr[j][z] );
			printf("\tcontent=%s", doc_list[i].content[j][z] );
			printf("\tcontent_id=%d", doc_list[i].content_id[j][z] );
		}
	}
	*/
	}

	 printf("\nmax_stack_count=%d\tdocid=%d", max_stack_count, max_docid );
}

static int t_count[NUM_DOCS] = {0};
static int t_count_var = 0;

static void
init_data_structures()
{
	//printf("\ninit_data_structures():");
	
	int i, j, k;

        for ( i=0; i < TABLE_SZ; i++)
        for ( j =0; j < MAX_CONTENTID; j++ )
              tag_id_table_count[i][j] = 0; 

	for ( i=0; i < TABLE_SZ; i++)
		tag_id_table[i] = 0;
	/*	
        for ( i=0; i < TABLE_SZ; i++)
                tag_table[i] = "";
	*/	
	//static const char tag_table[TABLE_SZ][MAX_ELE_SZ+1];
	/*
        for ( i=0; i < TABLE_SZ_SW; i++)
                stop_word_table[i] = "";
	*/
	//static const char stop_word_table[TABLE_SZ_SW][MAX_ELE_SZ+1];

        for ( i=0; i < TABLE_SZ; i++)
        for ( j =0; j < MAX_CONTENTID; j++ )
		tag_id_table_term[i][j] = 0;;

	/*
        for ( i=0; i < TABLE_SZ; i++)
        for ( j =0; j < MAX_CONTENTID; j++ )
	for ( k =0; k < 100; k++ )	
	 	tag_table_term[i][j][k] = 0;
	*/

        for ( i=0; i < TABLE_SZ; i++)
        for ( j =0; j < MAX_CONTENTID; j++ )
		idf[i][j] = 0.0;
 

	//init doc_list_sel
	for ( i=0; i<NUM_DOCS; i++)
	{
		doc_list[i].stack_count = 0;

		doc_list_sel[i].list_count = 0;

		for (j=0; j < MAX_CAND; j++ )
		{
                      doc_list_sel[i].tag_id[j] = 0;//t_tag_id;
                      doc_list_sel[i].content_id[j] = 0;//t_content_id;    
                      strcpy( doc_list_sel[i].content[j], "" );   
		}

		t_count[i] = 0;
	} 
	
	return;
}

static void
print_tables()
{
	int i, j;

	for ( i=0; i < 11 /*TABLE_SZ*/; i++)
	{
		printf("\ni=%d\ttag_table_count[]=%d", i, tag_table_count[i] );

		for ( j =0; j < MAX_CONTENTID; j++ )
		{
			//printf("\ni=%d\tj=%d\ttag_id_table_count[%d][%d]=%d", i, j, i, j, tag_id_table_count[i][j] );
			printf("\ni=%d\tj=%d\ttag_id_table_count[][]=%d\tcontent= %s", i, j, (tag_id_table_count[i][j]), tag_table_term[i][j]  );
		      	//        if ( tag_id_table_count[t_tag_id][t_content_id]  > 1 )
        	       	// if ( tag_id_table_count[t_tag_id][t_content_id]  < 100 )
		}
	}

	return;
}

static void
print_rp_nodes_select()
{
        int i, j, z;
	int temp;
	int t_tag_id;
	int t_content_id;
	int t_cnt;

        char *ch;
        char str_array[20][20];
        int str_count = 0;
        int x;
        char st1[100]="";
        int stop_word;


        for (i=0; i < document_count_plus - 1 ; i++)
        //for (i=0; i < 1000; i++)
        {
	for (j=0; j < doc_list[i].stack_count; j++)
        {       
		temp = doc_list[i].stack_size[j];

		t_tag_id = doc_list[i].tag_id[j][temp];
		t_content_id = doc_list[i].content_id[j][temp];
			
		if ( t_content_id > MAX_CONTENTID )
			continue;
		/*
		if ( t_tag_id != 3 ) //did
		if ( t_tag_id != 8 ) //title, special treatment later
		if ( t_tag_id != 10 ) //cdextra
		if ( t_tag_id != 11 ) //year	*/
		if ( t_tag_id < TABLE_SZ )
                if ( tag_table_count[t_tag_id] > 0 )
		{	
		if ( tag_id_table_count[t_tag_id][t_content_id]  > MIN_DF )
		if ( tag_id_table_count[t_tag_id][t_content_id]  < MAX_DF )
		{
			//populated 'doc_list_sel' with relavent entries
			t_cnt = doc_list_sel[i].list_count;
			
			if ( t_cnt < MAX_CAND )
			{							
				//select this stack
				doc_list_sel[i].tag_id[t_cnt] = t_tag_id;	
				doc_list_sel[i].content_id[t_cnt] = t_content_id;	
				strcpy( doc_list_sel[i].content[t_cnt], doc_list[i].content[j][temp] );		

				(  doc_list_sel[i].list_count )++;			
			}			
		}
		}
		/*	
	        //Add string splitter part here:        
        	if ( t_tag_id  == 8 ) //do this only for 'titles'
	        {
			strcpy( st1, doc_list[i].content[j][temp] );

	                //ch = strtok( doc_list[i].content[j][temp], " ");
	                ch = strtok( st1, " ");
			str_count = 0;

        	        while ( (ch != NULL) && ( str_count < 20 ) )
                	{
                        	//printf("\n%s", ch);
	                        strcpy(str_array[str_count], ch);
        	                //printf("\t: %s", str_array[str_count] );
                	        str_count++;
                        	ch = strtok(NULL, " ,");
	                }

	                for ( x=0; x < str_count; x++ )
        	        {
                	        //skip if entry is a 'stop word'
                        	stop_word = 0;
	                        if ( str_array[x] != NULL )
        	                {
	               	        	stop_word = SEARCH_stop_word( str_array[x] );

		                        if ( stop_word > 0 ) continue;
		                        if ( strlen( str_array[x] ) < 2 ) continue;                        	 
				}                
	                        //Now, search this term     
                		t_content_id = SEARCH_term( str_array[x], t_tag_id ); 

	                	if ( t_content_id > MAX_CONTENTID )
        	                	continue;

		                if ( tag_table_count[t_tag_id] > 0 )
                		if ( tag_id_table_count[t_tag_id][t_content_id]  > MIN_DF )
	        	        if ( tag_id_table_count[t_tag_id][t_content_id]  < MAX_DF )
        	        	{
                        		//populated 'doc_list_sel' with relavent entries
		                        t_cnt = doc_list_sel[i].list_count;

        		                if ( t_cnt < MAX_CAND )
        	        	        {
                                		//select this stack
	                	                doc_list_sel[i].tag_id[t_cnt] = t_tag_id;
        	                	        doc_list_sel[i].content_id[t_cnt] = t_content_id;
                	                	strcpy( doc_list_sel[i].content[t_cnt], str_array[x] );

	                        	        (  doc_list_sel[i].list_count )++;
        	                	}
                		}
                }
        	}*/		
        }
        }
}

static void
print_doc_list_sel(void)
{
	int list_count_1 = 0;
	int list_count_2 = 0;
	int list_count_5 = 0;

	int i,j,k;

	printf("\nstop_word_count = %d", stop_word_count );

	printf("\nprint_doc_sel(): using 'IDF' metric");

	for ( i=0; i < document_count_plus; i++ )
	{	
		if ( doc_list_sel[i].list_count > 0 )
		//if ( doc_list_sel[i].list_count > 1 )
		{
		printf("\ndocid=%d\tlist_count=%d", i, doc_list_sel[i].list_count );
		
			for ( j = 0; j < doc_list_sel[i].list_count; j++ )
			{
			//printf("\ttag_id=%d", doc_list_sel[i].tag_id[j] );
			//printf("\tcontent_id=%d", doc_list_sel[i].content_id[j] );
			printf("\tcontent(tag_id=%d)=%s", doc_list_sel[i].tag_id[j], doc_list_sel[i].content[j] );
			}
		}
		if ( doc_list_sel[i].list_count > 5 ) list_count_5++;
		else
		{	if ( doc_list_sel[i].list_count > 2 ) list_count_2++;
			else
				if ( doc_list_sel[i].list_count > 1 ) list_count_1++;
			
		}

	}
	printf("\nlist_count_1 = %d",list_count_1 );
	printf("\nlist_count_2 = %d",list_count_2 );
	printf("\nlist_count_5 = %d",list_count_5 );
	//exit(0);
}

static int num_edit_dist_calls = 0;
static int num_contentid_comp = 0;
static int num_tagid_comp = 0;

static void
identify_candidate_set(void)
{
	int i, j, k;
	int x, y, z;

	int cnt = 0;;
	int similarity_score = 0;

	char word1[MAX_CONTENT_SZ];
	char word2[MAX_CONTENT_SZ];
	char word3[MAX_CONTENT_SZ];
	//char word1[MAX_ELE_SZ];
	//char word2[MAX_ELE_SZ];
	//char word3[MAX_ELE_SZ];

	int len1;
	int len2;
	int d;

	float str_sim_score;	

	//for ( i = 1; i < 1000 ; i++)
	for ( i = 1; i < document_count_plus; i++)
	{
	
	//if ( doc_list_sel[i].list_count > 1 )
	//for ( x = 0; x < 5 ; x++)
	for ( x = 1; x < document_count_plus; x++)
	{
		//if ( cnt == 20 ) break;
		if ( cnt == MAX_CAND ) break;

		//if ( doc_list_sel[i].list_count > 1 ) 
		if ( i != x ) //skip comparion
		{
		//First: compare tag_id's
		for ( j = 0; j < doc_list_sel[i].list_count; j++ )
		{
		for ( y = 0; y < doc_list_sel[x].list_count; y++ )
		{
			if ( doc_list_sel[i].tag_id[j] == doc_list_sel[x].tag_id[y] )
			{
				num_tagid_comp++;

				//Second: compare content_id's	
				if ( doc_list_sel[i].content_id[j] == doc_list_sel[x].content_id[y] )	
				{	
					num_contentid_comp++;
					similarity_score++;				
				}
				else //Third: compare content's
				{
					len1 = 5; //strlen( doc_list_sel[i].content[j] );
					len2 = strlen( doc_list_sel[x].content[y] );
				
					if ( len1 > 0 )
					{
						num_edit_dist_calls++;

						strcpy( word3, doc_list_sel[i].content[j] );
						strcpy( word2, doc_list_sel[x].content[y] );
					
						d = distance (word3, len1, word2, len2);
						//d =  len1;//distance (word3, len1, word2, len2);
						num_string_comparisons1++;		
																
						str_sim_score = 1 - ((1.0)*d)/len1  ;
					
						//if ( str_sim_score > 0.50 )
						if ( str_sim_score > STR_SIM_THRESH )
						{ 
							similarity_score++;
							//printf("\nword=%s len1=%d\tword=%s len2=%d\tedit dist=%d\tstr_sim_score=%4.4f\n\n", word3, len1, word2, len2, d, str_sim_score );
						}
					}
				}
			}
		}//close for loop: 'y'
		}//close for loop: 'j'

		}

		//pick the doc 'x' if it is a relavent candidate 
		//if ( doc_list_sel[i].list_count > 0 )
		if ( doc_list_sel[i].list_count > 1 )
		//if ( (float)( similarity_score/(doc_list_sel[xi].list_count +1) ) > (float)THETA1*(0.1) )
		//if ( (float)( similarity_score / doc_list_sel[i].list_count ) > 0.50  )
		//if ( ( ((1.0)*similarity_score) / doc_list_sel[i].list_count ) > 0.70  )
		if ( ( ((1.0)*similarity_score) / doc_list_sel[i].list_count ) > ( CAND_SIM_THRESH  ) )
		{	
			cand_set_list[i].cand_doc[cnt] = x;
			//cand_set_list[i].cand_sim_score[cnt] = ((1.0)*similarity_score)/(doc_list_sel[i].list_count) ;
			cand_set_list[i].cand_sim_score[cnt] = (1.0)*similarity_score;
			//printf("\ni=%d\tx=%d\tcnt=%d\tsimilarity_score=%d\tlist_count=%d\tcand_sim_score=%1.2f", i, x, cnt, similarity_score, doc_list_sel[i].list_count, ((1.0)*similarity_score)/doc_list_sel[i].list_count );
			cnt++;
		}

		similarity_score = 0;
						
	}//close for loop: 'x'

		cand_set_list[i].count = cnt;
		cnt = 0;		

	}//close for loop: 'i'

	//printf("\nidentify_candidate_set(): exiting...");  exit(0);
	return;
}

static void
identify_duplicates(void)
{
        int i, j, k; //for document
        int x, y, z; //for candidate
        int cnt = 0;;
        int element_similarity_score = 0;
        int stack_similarity_score = 0;
        //int cand_similarity_score = 0;
        float cand_similarity_score = 0;

	char word1[MAX_CONTENT_SZ];
	char word2[MAX_CONTENT_SZ];
	char word3[MAX_CONTENT_SZ];
	//char word1[MAX_ELE_SZ];
	//char word2[MAX_ELE_SZ];
	//char word3[MAX_ELE_SZ];

	//const char * word1;
	//const char * word2;
	int len1;
	int len2;
	int d;

	int curr_docid = 0;
	int cand_docid = 0;
	int curr_stackid = 0;
	int cand_stackid = 0;
	
        float str_sim_score;

	int overall_sim_score = 0;

        //for ( i=0; i < 5; i++ )
        for ( i=0; i < document_count_plus; i++ )
        {
		curr_docid = i;
		

                //for ( x=0; (x < cand_set_list[i].count) && (x < 20); x++ )
                for ( x=0; (x < cand_set_list[i].count) && (x < MAX_CAND); x++ )
                {
			
			cand_docid = cand_set_list[i].cand_doc[x];

			//check this candidate for duplicity. 			//NOTE: we assume to be 'schema-aware' ('schema-oblivious' is to be implemented).
			//Here top-most entity is 'object' to be detected. 	
			//We use bottom-up approach for detection (start from leaf node and move up the stack (or path to root node i.e. 'object' to be detected))
                        //printf("\t%d (%1.2f)", cand_set_list[i].cand_doc[j], cand_set_list[i].cand_sim_score[j] );

	                for ( j=0; j < doc_list[curr_docid].stack_count; j++ )
			{				
		        	curr_stackid = j;

	                for ( y=0; y < doc_list[cand_docid].stack_count; y++ )
        	        {
				stack_similarity_score = 0;
                	        cand_stackid = y;
				
				k = doc_list[i].stack_size[j];	
				//z = doc_list[x].stack_size[y];
				z = doc_list[cand_docid].stack_size[y];

				//printf("\n loop y, exiting..."); exit(0);

				for ( k = doc_list[i].stack_size[j]; ( k >= 0 ) && ( z >= 0 ); k-- && z-- )
				//for ( k = 0; k <= doc_list[i].stack_size[j]; k++ && z-- )
				{
					element_similarity_score = 0;

					//printf("\n1: loop k, exiting"); exit(0);

					//First level: compare tag_is's
					if ( doc_list[i].tag_id[j][k] == doc_list[cand_docid].tag_id[y][z] )
					{
					
						//printf("\n2: loop k, exiting"); exit(0);

						//Second level: compare content_id's  
		                                if ( doc_list[i].content_id[j][k] == doc_list[cand_docid].content_id[y][z] )
        		                                 element_similarity_score++;
					                        	        
                	                	else //Third level: compare content's
                        	        	{
                                	        	len1 = 5; //strlen( doc_list[i].content[j][k] );
                                        		len2 = strlen( doc_list[cand_docid].content[y][z] );

	                                        	if ( len1 > 0 )
        	                                	{
                	                        	strcpy( word3, doc_list[i].content[j][k] );
	                	                        strcpy( word2, doc_list[cand_docid].content[y][z] );

        	                	                d = distance (word3, len1, word2, len2);
							
							num_string_comparisons2++;
							
        	                        	        str_sim_score = 1.0 - ((1.0)*d)/len1  ;

                	                        	//if ( str_sim_score > 0.50  )
                	                        	if ( str_sim_score > STR_SIM_THRESH )
                        	                        	element_similarity_score++;
                                        		}
						}
                          		}//end of 'IF'

					if ( element_similarity_score > 0 )
					{	stack_similarity_score++;
						//printf("\nstack_similarity_score=%d, exiting", stack_similarity_score ); //exit(0);
					}
					else	break;
					
				}//end of 'k' 'FOR' loop

				//if ( stack_similarity_score > 1 )
				//if ( stack_similarity_score > 2 )
				if ( stack_similarity_score > 3 )
				{
					//done with matching this 'stack', now pick next stack 
					cand_similarity_score++;
					//printf("\ni=%d\tx=%d\tcand_similarity_score=%d, exiting", i, x, cand_similarity_score ); //exit(0);
					break;	
				}
				//else check with next stack of the candidate doc
                	}//end of 'y' 'FOR' loop
		}//end of 'j' 'FOR' loop
				
		//if ( cand_similarity_score >= 10 )
		//if ( cand_similarity_score >= 5 )
		//if ( cand_similarity_score >= (doc_list[i].stack_count) )
		if ( ( cand_similarity_score >= (1.0)*(doc_list[i].stack_count)/2 ) || 
		   ( cand_similarity_score >= (1.0)*(doc_list[x].stack_count)/2 ) )
		//if ( cand_similarity_score >= ( (doc_list[i].stack_count) >> 2 ) )
		{ 
		        duplicate_set_list[i].cand_doc[cnt] = cand_docid;
       	                duplicate_set_list[i].cand_sim_score[cnt] = (float) cand_similarity_score;
			cnt++;
			//printf("\nduplicate found\ti=%d\tcand_docid=%d\tcand_similarity_score=%4.2f\tstack_count=%d", i, cand_docid, (float) cand_similarity_score, doc_list[i].stack_count); //exit(0);
		}

		cand_similarity_score = 0;	
 
	       	}//end of 'x' 'FOR' loop

                duplicate_set_list[i].count = cnt;
                cnt = 0;

        }//end of 'i' 'FOR' loop

	//exit(0);

        return;
}


void print_cand_list(void)
{
	int i, j;

	//printf("\nstop_word_count = %d", stop_word_count );

	for ( i = 0; i < document_count_plus; i++ )
	{
		if ( cand_set_list[i].count > 0 )
		{
		printf("\ndocid=%d\tcandidate count=%d\n", i, cand_set_list[i].count );
			
			//for ( j=0; (j < cand_set_list[i].count) && (j < 20); j++ )
			for ( j=0; (j < cand_set_list[i].count) && ( j < MAX_CAND ); j++ )
			{		
			printf("\t%d (%1.2f)", cand_set_list[i].cand_doc[j], cand_set_list[i].cand_sim_score[j] );
			}
		
		}
	}
} 

void print_duplicate_list(void)
{
        int i, j, k;
	int x, y, z;
	int count = 0;
	int total_duplicates;	
	int total_duplicates1;
	int temp = 0;

        for ( i = 0; i < document_count_plus; i++ )
        {
		total_duplicates = 0;
		if ( duplicate_set_list[i].count > 0 )
		{
                //printf("\ndocid=%d\tduplicate count=%d\n", i, duplicate_set_list[i].count );
				
                //for ( j=0; (j < duplicate_set_list[i].count) && (j < 20); j++ )
                for ( j = 0; (j < duplicate_set_list[i].count) && (j < MAX_CAND); j++ )
                {
                        //printf("\t%d (%1.2f)", duplicate_set_list[i].cand_doc[j], duplicate_set_list[i].cand_sim_score[j] );
			total_duplicates++;

			x = duplicate_set_list[i].cand_doc[j];
			duplicate_matrix[i][x] = 1;
			/*
			//now print transitive duplicates:
	                if ( duplicate_set_list[x].count > 0 )
	                {
        	        	//printf("\ndocid=%d\tduplicate count=%d\n", x, duplicate_set_list[x].count );
	                	//for ( y=0; (y < duplicate_set_list[x].count) && (y < 20); y++ )
	                	for ( y=0; (y < duplicate_set_list[x].count) && (y < MAX_CAND); y++ )
                		{	
					//printf("\t%d (%1.2f)", duplicate_set_list[x].cand_doc[y], duplicate_set_list[x].cand_sim_score[y] );

					z = duplicate_set_list[x].cand_doc[y];

					duplicate_matrix[i][z] = 1;
					total_duplicates++;
				}
			}
			*/
                }	
		}

		total_duplicates1 = 0;

		if ( total_duplicates > 0 ) 
		{
			if ( i > 259 ) 
				printf("\n%d", (i % 259 ) );
			else printf("\n%d", i );

			//for ( k=0; k <= 1878; k++ )
			for ( k = 0; k < NUM_DOCS; k++ )
			{
				if ( duplicate_matrix[i][k] == 1 )
				{
					//duplicate_matrix[k][i] == 1;
					//printf("\t%d", k );
					//if ( total_duplicates1++ > 9 ) break;

					if ( i != k )
					{
						if ( i < 259 )
							printf("\t%d", (k % 259) );
						else
							printf("\t%d", k );
				
						if ( total_duplicates1++ == 7 ) break;
					}
				}
			}

		//pad '0's
		//for ( temp = total_duplicates1; temp < 10; temp++ ) 
		for ( temp = total_duplicates1; temp < 8; temp++ ) 
			printf("\t0");

		}	
        }
}

void print_duplicates1(void)
{
	int i, k;
	int total_duplicates1 = 0;

	//for ( i=0; i <= 1878; i++ )
	for ( i=0; i < NUM_DOCS; i++ )
	{
		
	      //for ( k=0; k <= 1878; k++ )
	      for ( k=0; k < NUM_DOCS; k++ )
              {
              	if ( duplicate_matrix[i][k] == 1 )
                {
                	//duplicate_matrix[k][i] == 1;
                        printf("\t%d", k );
                        total_duplicates1++;
                }
             }
		
             printf("\ndocid=%d\ttotal_duplicates1=%d\n", i, total_duplicates1 );
		total_duplicates1 = 0;
	}	
}

static int is_root_node = 1;
int linesread = 0;

//int content_len = 0;
void
handle_data(void *data, const char *content, int length)
{
	char *tmp = malloc(length);

	//limit the size of content to MAX_CONTENT_SZ (=40)
	if ( length > MAX_CONTENT_SZ -1 )
		length = MAX_CONTENT_SZ -1 ;
	
	strncpy(tmp, content, length);
	tmp[length] = '\0';
	data = (void *) tmp;
	last_content = tmp;         /* TODO: concatenate the text nodes? */

	content_len = length;
}

static void XMLCALL
start1(void *data, const char *el, const char **attr);

static void XMLCALL
start(void *data, const char *el, const char **attr)
{
	int i;
	int len;

	int tag = -1;
	int node_degree;
	int doc_start = 0;
	//short start_symbol = 0xFFFF;
	//short start_symbol = 256;
	short start_symbol = 128;

/*
	printf("\n");
	for ( i =0; i < Depth; i++ )
		printf("\t");
		printf("%d:", Depth);

	printf("%s:", el );
	
        for (i = 0; attr[i]; i += 2) {
            printf("i=%d %s=%s",i, attr[i], attr[i + 1]);
	}

	Depth++;
return ;
*/	
	//search or insert
	len=strlen(el);

	tag = SEARCH(el, 1 );

	//for cora_RADD data set:
	if ( BENCH == 1)
	{
		if ( tag == 4 ) {
			document_count++;
			doc_start = 1;
		}
	}
        if ( BENCH == 2)
        {	//for FreeDB data set
                if ( tag == 2 ) {
			document_count++;
			doc_start = 1;
		}
        }
	
	if ( BENCH == 3 )
	{	//for CountryDB data set:
		if ( tag == 1 ) {
			document_count++;
			doc_start = 1;
		}
	}	
	/*
	if ( document_count >=  NUM_DOCS - 1 ) 
	{
		printf("\nafter document_count %d", document_count );
		print_rp_nodes_select();
		return; 
		//exit(0);	
	}
	*/

	last_tag = (short) tag;
	//printf("\nstart: docid=%d\ttag is=%d", document_count, tag);
		
	//update degree of current node, as we are goinng to visit a child node	
	//update_node_degree();
	
	//sanity check
	if ( curr_stack_ptr >= MAX_TOP_STACK )
	{ 	
		strcpy( error_msg, "stack overflow:curr_stack_ptr >= MAX_TOP_STACK"); 
		//exception_handler( error_msg, curr_stack_ptr, "encode_node_rp" );
		printf("\ncurr_stack_ptr : %d \tMAX_TOP_STACK: %d\tdocument_count=%d\tlast_tag=%d\tel=%s", curr_stack_ptr, MAX_TOP_STACK, document_count, last_tag, el );
		exception_handler( error_msg, curr_stack_ptr, "encode_node_rp" );
		//exit(-1);
	}

	//push to rp_nodelist: code implemented here only

	//printf("\n START: el=%s \t last_content=%s", el, last_content);

	//start_symbol = ( start_symbol << 8 ) && tag;
	start_symbol = start_symbol + tag;
	//rp_nodelist[curr_rp_node_ptr] = (short) tag;
	rp_nodelist[curr_rp_node_ptr] = (short) start_symbol;
	if ( doc_start ) {
		document[document_count].docid = document_count;
		document[document_count].start = curr_rp_node_ptr;
	}
	//document[document_count].start = curr_rp_node_ptr;
	curr_rp_node_ptr++;

	/*	
        curr_stack_ptr++;

        last_tag_pushed = stack_rp[curr_stack_ptr].tag_id = tag;

	if ( attr[0] && attr[1] ) 
        	strcpy( stack_rp[curr_stack_ptr].attr, attr[1] );
	else strcpy( stack_rp[curr_stack_ptr].attr, "" );
	*/

	Depth++;

	//increment pre-prder traversal number
	pre_order_trav_number++;

return;

	/*
	//testing
	if ( Depth > 0) 
	if ( is_root_node )
	{
		is_root_node = 0;
	//print_rp_nodes();
	//print_stack();
	//printf("\ntag_index_matrix[0].val=%d", tag_index_matrix.val[0]);
	//printf("\ntag_id_ctr[0]=%d", tag_id_ctr[0]);
	old_curr_stack_ptr = curr_stack_ptr;
	old_curr_rp_node_ptr = curr_rp_node_ptr;

	old_rp_nodelist_tag_id = rp_nodelist[0].tag_id; 
	old_rp_nodelist_n_degree = rp_nodelist[0].n_degree;

	old_stack_rp_tag_id = stack_rp[0].tag_id;
	old_stack_rp_n_degree = stack_rp[0].n_degree;

	old_last_tag_pushed = last_tag_pushed;
	}
	*/
}

static int num_bytes_parsed = 0;

static void XMLCALL
end1(void *data, const char *el);

static int tt_count = 0;

static void XMLCALL
end(void *data, const char *el)
{
	//int tag;
	short term_tag = -1;
	int len = 0;
	Depth--;
	
	char *ch;
	char str_array[20][20];
	int str_count = 0;
	int i;
	char st1[100]="";
	int stop_word;

	short end_symb = 192;

	/*
	printf("\t:end:%s", el);
	return;
	*/
	if ( document_count >=  NUM_DOCS - 1 )
		return;

	int tag = -1;
	int doc_end = 0;

        //search or insert
        len=strlen(el);

        tag = SEARCH(el, 0 );

        //for cora_RADD data set:
        if ( BENCH == 1)
        {
                if ( tag == 4 ) {
                        //document_count++;
                        doc_end = 1;
                }
        }
        if ( BENCH == 2)
        {       //for FreeDB data set
                if ( tag == 2 ) {
                        //document_count++;
                        doc_end = 1;
                }
        }

        if ( BENCH == 3 )
        {       //for CountryDB data set:
                if ( tag == 1 ) {
                        //document_count++;
                        doc_end = 1;
                }
        }
	/*
	end_symb = end_symb + tag;

        //push to rp_nodelist: code implemented here only
        //rp_nodelist[curr_rp_node_ptr] = (short) tag;
        rp_nodelist[curr_rp_node_ptr] = end_symb;
        if ( doc_end ) {
                //document[document_count].docid = document_count;
                //document[document_count].start = curr_rp_node_ptr;
	        document[document_count].end = curr_rp_node_ptr;
	}
        curr_rp_node_ptr++;
	*/

	//printf("\n END: el=%s \t last_content=%s", el, last_content);
	/*
	//push attr to stack:
	if ( ! last_content )
		strcpy( stack_rp[curr_stack_ptr].content, last_content);
	*/

        //search or insert
        len=strlen(el);

	//sanity check
        if( len >= MAX_ELE_SZ ){
		error_msg[80]="len >= MAX_ELE_SZ";
		exception_handler( "len >= MAX_ELE_SZ", len, "end" );
	}

        if( curr_rp_node_ptr >= MAX_INPUT_SZ ){ 
		error_msg[80]="curr_rp_node_ptr >= MAX_INPUT_SZ";
		printf("\ncurr_rp_node_ptr=%d\tMAX_INPUT_SZ=%d", curr_rp_node_ptr, MAX_INPUT_SZ ); 
		exception_handler( "curr_rp_node_ptr >= MAX_INPUT_SZ", 0 , "end");
	}	
	/*
       	strcpy( stack_rp[curr_stack_ptr].content, last_content);
	*/
	/*
	if (( document_count > 259 ) && ( document_count < 259 + 10 ) )
	printf("\n END: el=%s \t tag=%d \t last_content=%s \t content_len=%d", el, tag, last_content, content_len );
	*/
	//if (( document_count > 259 ) && ( document_count < 259 + 10 ) )
	//if ( ( last_content[0] != '\t' ) || (last_content[1] != '\t') ) 
	if ( ( last_content[0] != '\t' ) ) 
	{
	//if ( last_content ){	
	       	term_tag = SEARCH_term( last_content, last_tag );
	
		//if (( document_count > 259 ) && ( document_count < 259 + 10 ) )
		//printf("\t last_tag=%d \t term_tag=%d \t content_len=%d \t last_content[0](dec) = %d %d", last_tag, term_tag, content_len, last_content[0], last_content[1] );
	//}
	
	//put only valid values; discard junk values if any.
	if ( ( term_tag >= 0 ) && ( term_tag < MAX_CONTENTID ))	{	
		/*
		stack_rp[curr_stack_ptr].content_id = term_tag;
		*/
	       	//update count
		if ( last_tag != 0 )
        	( tag_id_table_count[last_tag][term_tag] )++;

		//if ( tt_count++ > 10000 ) { print_tables();	exit(0);}
		if ( last_tag == 0 ) 
			printf("\nlast_tag=%d\tterm_tag=%d\tcount=%d", last_tag, term_tag, tag_id_table_count[last_tag][term_tag] );
		
		//push to rp_nodelist[]:
		rp_nodelist[curr_rp_node_ptr] = (short) term_tag;
		curr_rp_node_ptr++;

		//if (( document_count > 259 ) && ( document_count < 259 + 10 ) )
		//printf("\t term_tag = 0x%3x", term_tag );
	
	}
	}

        end_symb = end_symb + tag;

        //push to rp_nodelist: code implemented here only
        //rp_nodelist[curr_rp_node_ptr] = (short) tag;
        rp_nodelist[curr_rp_node_ptr] = end_symb;
        if ( doc_end ) {
                //document[document_count].docid = document_count;
                //document[document_count].start = curr_rp_node_ptr;
                document[document_count].end = curr_rp_node_ptr;
        }

        curr_rp_node_ptr++;
	/*
	//encode only leaf nodes
	if ( ( term_tag >= 0 ) && ( term_tag < MAX_CONTENTID ))	{
		if ( last_tag_pushed == stack_rp[curr_stack_ptr].tag_id )
                        encode_node_rp();
	}

	//sanity check; only if their is some element in stack
	if ( curr_stack_ptr < 0 ){ 
		strcpy( error_msg, "stack unnderflow: curr_stack_ptr < 0"); 
		exception_handler( error_msg, curr_stack_ptr, "encode_node_rp" );
	}
	*/
	//pop stack
	//pop_stack();

	//if ( document_count > 10 ) exit(0);

return;

}

void init_arrays()
{
	return;
}

void re_init_arrays()
{
}

/*query reading*/
static void read_query_file()
{
}

/*read_query_file*/
void print_input();
void decompose_doc(void);

static int element_count=0;

int task_outcome_flag = 0;

//extern void kernel_wrapper(short * a);
/*
extern void kernel_wrapper( int num, struct query_ent * query_info, struct stack_ent * query_array , struct stack_ent * rp_nodelist, struct MyMat * tag_index_matrix, int * tag_id_ctr );
*/
/*Good for version2 (encode-rootpath2.c and query2.cu)
extern int kernel_wrapper( int num, query_ent * query_info, stack_ent * query_array , stack_ent * rp_nodelist, MyMat * tag_index_matrix, int * tag_id_ctr, int curr_rp_node_ptr );
*/
/*Kernel for version 3*/
//extern int kernel_wrapper( int num, query_ent * query_info, stack_ent * query_array , stack_ent * rp_nodelist, int * tag_index_array, int * tag_id_ctr, int curr_rp_node_ptr, int * tag_index_array_offset, int total_tags );
//extern int _query_matches(void);
//extern int kernel_wrapper(int t_num, sp_per * SP_personality, node * input_doc, int curr_rp_node_ptr, q_ent * query_index, int num_q_nodes );

//extern int kernel_wrapper(int t_num, int document_count, doc_metadata * document, short * rp_nodelist );
extern int kernel_wrapper(int t_num, int document_count, doc_metadata * document, short * rp_nodelist, int curr_rp_node_ptr );

int dummy_call_kernel_wrapper(void)
{

	//COMMENT: to hide device init latency
	int t_num = 1;
	//kernel_wrapper( t_num, query_info1, query_array, rp_nodelist, tag_index_matrix, tag_id_ctr, curr_rp_node_ptr );
 	//kernel_wrapper( t_num, query_info1, query_array, rp_nodelist, tag_index_array, tag_id_ctr, curr_rp_node_ptr, tag_index_array_offset, 0 );

	//fprintf(stdout, "\ndummy_call_kernel_wrapper:");
	return;
}

static time_t GPU_kernel_time = 0;

int t_count_num_tags;


int main(int argc, char *argv[])
{
	time_t  t0, t1, t2, t3, tn; /* time_t is defined on <time.h> and <sys/types.h> as long */
	clock_t c0, c1, cn; /* clock_t is defined on <time.h> and <sys/types.h> as int */
	int t_num = 0;
	
	long count;
	double a, b, c;

	char charbuf[16] = {0}; 

	init_data_structures();
	//print_tables();

	print_params();

	decompose_doc();

	t0 = time(NULL);
	c0 = clock();

	dummy_call_kernel_wrapper();
	//DOC_SEG_SIZE = 10000; //atoi(argv[2]);	//LINES_TO_SKIP = 0; //atoi(argv[1]); 	//BENCH = 1; //atoi(argv[3]);  	//BENCH = 2; //atoi(argv[3]); 

	read_tag_table();

	t0 = time(NULL);
	c0 = clock();

	read_stop_word_table();

  	p = XML_ParserCreate(NULL);
	  if (! p) {		fputs("Couldn't allocate memory for parser\n", stdout);	    exit_fn(-1); }
	XML_SetElementHandler(p, start, end);
        XML_SetCharacterDataHandler(p, handle_data);

	int i=0;
	int done1=0;

	while ( fgets(Buff, BUFFSIZE-1, stdin)) 
	{
	    int done;
	    int len;
	    len	= strlen( Buff );
	    done = feof(stdin);

	    if ( ! exit_fn_flag )
	    if ( ! XML_Parse(p, Buff, len, done) ) 
		{
      			fputs("Parse error at line", stdout);
			 sprintf( charbuf, "%d", XML_GetCurrentLineNumber(p) );
			 fputs( charbuf, stdout ); fputs("  \n", stdout );
        		done = 1; 
		}
	    if (done) break;
	}/*end of while*/

	XML_ParserFree(p);

	document_count_plus = document_count + 1;

	//Stage2
	print_rp_nodes_select();

	t1 = time(NULL);

	//identify_candidate_set();
	//print_cand_list();

	t2 = time(NULL);

	//printf("\nidentify_duplicates():");
	//identify_duplicates();

	t3 = time(NULL);

	//printf("\nprint_duplicates():");
	//print_duplicate_list();

	tn = time(NULL);
	
	printf("\n stop_word_count = %d", stop_word_count );
	printf("\n num_string_comparions1 = %d", num_string_comparisons1 );
	printf("\n num_string_comparions2 = %d", num_string_comparisons2 );

	printf("\n NUM_DOCS = %d", NUM_DOCS );
	printf("\n MAX_INPUT_SZ = %d", MAX_INPUT_SZ );
	printf("\n curr_rp_node_ptr = %d", curr_rp_node_ptr );
	printf("\n document_count = %d", document_count );
	printf("\n\n");

	//print_pre_post_tree_seq();
	//find_duplicates_pre_post_tree_seq();

	kernel_wrapper(t_num, document_count, document, rp_nodelist, curr_rp_node_ptr);
	
	return 0;

}/*end of main*/

void compare_pre_post_tree_seq(int start_idx1, int end_idx1, int start_idx2, int end_idx2, int idx1, int idx2) 
{	/*
	int ref_tree_start_idx = start_idx1;
	int ref_tree_end_idx = end_idx1;
	int cand_tree_start_idx = start_idx2;
	int cand_tree_end_idx = end_idx2;
	*/
	int ref_tree_size = end_idx1 - start_idx1 + 1 ;
	int cand_tree_size = end_idx2 - start_idx2 + 1 ;

	unsigned short ref_tree[ref_tree_size];
	unsigned short cand_tree[cand_tree_size];
	unsigned short out_XOR[ref_tree_size];

	int num_iter = 0;
	//int max_iter = 1;
	//int max_iter = 4;
	//int max_iter = 10;
	//int max_iter = ref_tree_size / 2;
	int max_iter = ref_tree_size;
	int i;
	int j;
	int temp;
	int new_ref_tree_size = 0;
	int temp_idx;
	//int mod_val = document_count + 1;
	int mod_val = 1878;

	//init out_XOR tree
	for (i=0; i < ref_tree_size; i++){	out_XOR[i] = 0;		}

	//copy ref and cand trees
	for (i=0; i < ref_tree_size; i++){ ref_tree[i] = rp_nodelist[start_idx1 + i];	}

	//copy ref and cand trees
	for (i=0; i < cand_tree_size; i++){ cand_tree[i] = rp_nodelist[start_idx2 + i];	}

	j = 0;
	new_ref_tree_size = ref_tree_size;

	while( num_iter++ < max_iter ){

		for ( j=0; j < new_ref_tree_size; j++ ){
			out_XOR[j] = ( ref_tree[j] )^( cand_tree[j] );
		}

		temp = 0;
		//drop matching chunks
		for ( i=0; i < new_ref_tree_size; i++) {
			if ( out_XOR[i] != 0 ) { //then retain the element
				ref_tree[i] = ref_tree[i];
				cand_tree[i] = cand_tree[i];			
				temp++;
			}
			else { //search for next non-zero element
				temp_idx = i;
				while ( ++temp_idx < new_ref_tree_size ) {
					if ( out_XOR[temp_idx] != 0 )
						break;
				}
				if ( temp_idx == new_ref_tree_size )
					break;
				else {
                                	ref_tree[i] = ref_tree[temp_idx];
	                                cand_tree[i] = cand_tree[temp_idx];
        	                        temp++;
				}
			}
		}

		for (i=0; i < ref_tree_size; i++){	out_XOR[i] = 0;		}

		new_ref_tree_size = temp;
		//printf("\n new_ref_tree_size = %d", new_ref_tree_size);

		if ( !new_ref_tree_size ){
			//printf("\n tree match: docs: %d (idx1 mod 259 = %d), %d (idx2 mod 259 = %d)", idx1, (idx1 % 259), idx2, (idx2 % 259) );
			printf("\n tree match: docs: %d (idx1 mod 259 = %d), %d (idx2 mod 259 = %d)", idx1, (idx1 % mod_val), idx2, (idx2 % mod_val) );

			break;
		}
	}
}	

void print_pre_post_tree_seq()
{
	int i;
	int j;
	//for ( i=0; i < curr_rp_node_ptr; i++ )
	for ( i=0; i < 1000; i++ ){
		//j = i + document[259].end + 1;
		j = i + 28995 ;
		printf("\n (%3d) \t 0x%4x (%5d)\t 0x%4x", i, rp_nodelist[i], j, rp_nodelist[j] );
	}

	printf("\n\n");

	//for ( i=curr_rp_node_ptr - 20; i < curr_rp_node_ptr; i++ )		printf("\n %d", rp_nodelist[i] );

	for ( i=1; i < document_count; i++ ){
		printf("\n %d", document[i].docid );
		printf("\t %d", document[i].start );
		printf("\t %d", document[i].end );
		printf("\t %d", document[i].end  - document[i].start );
	}
}

void find_duplicates_pre_post_tree_seq()
{
        int i;
	int j;
	
        for ( i=1; i < document_count; i++ ){
		for ( j=1; j < document_count; j++){		
		if ( i != j ){
			//compare_pre_post_tree_seq( document[i].start, document[i].end, document[259 + j].start, document[259 + j].end, i, 259 + j );
			compare_pre_post_tree_seq( document[i].start, document[i].end, document[j].start, document[j].end, i, j );
		}
		}
        }
	
	/*
	int max = 0;
	int diff = 0;
        for ( i=1; i < document_count; i++ ){
		diff = document[i].end - document[i].start;

		if ( diff > max )
			max = diff;
                }
	printf("\n max = %d", max);
	exit(0);
	*/
}

void print_term_freq()
{
	int i,j;
		printf("\n\nlog10(document_count ) \t= %4.4f", log10(document_count) );
		printf("\nlog10(document_count / 1 ) \t= %4.4f", log10(document_count/1) );
		printf("\nlog10(document_count / 2 ) \t= %4.4f", log10(document_count/2) );
		printf("\nlog10(document_count / 5 ) \t= %4.4f", log10(document_count/5) );
		printf("\nlog10(document_count / 10 ) \t= %4.4f", log10(document_count/10) );
		printf("\nlog10(document_count / 100 ) \t= %4.4f\n", log10(document_count/100) );
		printf("\nlog10( 10 ) \t= %4.4f", log10( 10 ) );
		printf("\nlog10( 2 ) \t= %4.4f", log10( 2 ) );
		printf("\nlog10( 1 ) \t= %4.4f\n\n", log10( 1 ) );
}

static int gpu_filter_fn_count=0;
static int gpu_filter_fn_attempt_count = 0;

void gpu_filter_fn(void)
{
	return;
}

void print_input()
{
}

int data_packing(void)
{
}

#define MAX_MEMORY_AVAILABLE 1  //(in MB)

void decompose_doc(void)
{
}

int t_max_depth;

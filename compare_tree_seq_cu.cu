#include "b.h"
#include "inputfile.h"
#include "structdef.h"
#include "structures.h"
#include "device_functions.h"
#include "cuda.h"
#include "cuda_runtime.h"
#include <pthread.h>
#include <unistd.h>
#include <stdlib.h>
#include "time.h"

#define DEBUG 0

//final querying output
typedef struct t_q_res{
unsigned match_count;
}query_res;

static query_res QueryResult[MAX_NUM_QUERY];

extern "C" int output_query_matches(void);
//all the cuda related functions
#include "header.h"

//forward declarations
void print_input();
void verify_result( MyMatch * match, unsigned int Q );

extern "C" int kernel_wrapper(int t_num, int document_count, doc_metadata * document, short * rp_nodelist, int curr_rp_node_ptr );

#define BLOCK_SZ 256
#define BLOCK_SZ 1024
#define MAX_TREE_SEQ_SIZE 1200

__global__ void GPU_kernel( int N, doc_metadata * document, short * rp_nodelist, int * match_state, int threadsPerBlock, int curr_rp_node_ptr )
{	
	int RefTreeID;
	int CandTreeID;

	int start_idx1, end_idx1, start_idx2, end_idx2;
        int ref_tree_size;
        int cand_tree_size;

        unsigned short ref_tree[MAX_TREE_SEQ_SIZE];
        unsigned short cand_tree[MAX_TREE_SEQ_SIZE];
        unsigned short out_XOR[MAX_TREE_SEQ_SIZE];

        int num_iter;
        int max_iter = 1;
        //int max_iter = 4;
	//int max_iter = 10;
        int i, j, temp;
        int new_ref_tree_size = 0;
        int temp_idx;

	int NumBlocks = N/BLOCK_SZ;

	//if ( blockIdx.y < N )
	if ( blockIdx.x <= N )
	{ 
	//if ( threadIdx.x < threadsPerBlock )
	if ( threadIdx.x <=  N )
	{
		//RefTreeID = blockIdx.y + 1;
		RefTreeID = blockIdx.x + 1;
        	start_idx1 = document[RefTreeID].start;
                end_idx1 = document[RefTreeID].end;
	        ref_tree_size = end_idx1 - start_idx1 + 1;

		max_iter = ref_tree_size;

	       	for (i=0; i < ref_tree_size; i++)	{ ref_tree[i] = rp_nodelist[start_idx1 + i];   }
                //init out_XOR tree
                for (i=0; i < ref_tree_size; i++)	{    out_XOR[i] = 0;    }

		//CandTreeID = (blockIdx.x)*(BLOCK_SZ) + threadIdx.x + 1;
		//CandTreeID = threadIdx.x + 1 + 259;
		CandTreeID = threadIdx.x + 1;

		if ( RefTreeID != CandTreeID )
		{
	                start_idx2 = document[CandTreeID].start;
        	        end_idx2 = document[CandTreeID].end;
                	cand_tree_size = end_idx2 - start_idx2 + 1;

		        for (i=0; i < cand_tree_size; i++)	{ cand_tree[i] = rp_nodelist[start_idx2 + i]; }
		        new_ref_tree_size = ref_tree_size;

			num_iter = 0;

	        	while( num_iter++ < max_iter ){
				
                		for ( j=0; j < new_ref_tree_size; j++ ){
                        		out_XOR[j] = ( ref_tree[j] )^( cand_tree[j] );
                		}
	                	temp = 0;

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

	                	for (i=0; i < ref_tree_size; i++)	{      out_XOR[i] = 0;         }

        	        	new_ref_tree_size = temp;	
				
                		if ( !new_ref_tree_size ){
					match_state[RefTreeID ] = CandTreeID;			
		                        break;
        	        	}
	        	}//end of WHILE loop
		}//end of IF
	}//end of thread	
	}//end of block
	//}//end of grid

	return;
}//end of kernel

static int no_device_yet = 1; 
static int grab_gpu_device_attempt = 0;

int kernel_wrapper(int t_num, int document_count, doc_metadata * document, short * rp_nodelist, int curr_rp_node_ptr )
{
	unsigned int r;	int i;
	unsigned int r1;
	int num = t_num;
	//int match_state[520];
	int match_state[1879*2];

	//init match_state
	//for (i=0; i < 520; i++)	match_state[i] = -1;
	for (i=0; i < 1879*2; i++)	match_state[i] = -1;

       	srand( time(NULL) );	r = rand() % 10000;   	usleep ( r );         fprintf(stdout, "\nsleeping for r=%d second\n", r/1000000);
	
        no_device_yet = grab_gpu_device(); 

        while ( no_device_yet == 1 ) {	
		r = rand();	        r1 = ( 2000000 + ( r % 4000000 ));
	        fprintf(stdout, "\nr1=%d", r1); fprintf(stdout, "\nsleeping for r1=%d second", r1/1000000);
		usleep ( r1 );
	        //task_outcome_flag = kernel_wrapper( t_num, query_info1, query_array, rp_nodelist, tag_index_matrix, tag_id_ctr, curr_rp_node_ptr );
        	no_device_yet = grab_gpu_device(); 	        grab_gpu_device_attempt++;
        	if ( grab_gpu_device_attempt >= 4 ) 		{  	return 1;	}
        }

	//dummy code to initiate driver initialization
	if (num == 1)	{
	        MyMatch * d_a1;        	int size1 = sizeof( MyMatch ); 		
		cudaMalloc( (void **)&d_a1, size1*1 );	fprintf(stdout, "\ndummy call");	return 0;
	}

	doc_metadata * d_document;	short * d_rp_nodelist;	int * d_match_state;

        srand( time(NULL) );         r = rand() % 10000;         usleep ( r );        no_device_yet = grab_gpu_device();

        while ( no_device_yet == 1 )
        {       r = rand();	r1 = 0 ;
                if (DEBUG) fprintf(stdout, "\n sleeping for r1=%d second", r1/1000000);
                usleep ( r1 );                 no_device_yet = grab_gpu_device();
                grab_gpu_device_attempt++;
                if (DEBUG) fprintf(stdout, "\n grab_gpu_device_attempt=%d", grab_gpu_device_attempt );
                if ( grab_gpu_device_attempt >= 4 )	return 1;
        }

	clock_t start1=clock();		printf("\n start:%lu\n", start1 );

	int N = document_count;

	cudaMalloc((void**)&d_document, sizeof(doc_metadata)*N );
	cudaMalloc((void**)&d_rp_nodelist, sizeof(short)*curr_rp_node_ptr );
	cudaMalloc((void**)&d_match_state, sizeof(int)*N );

	//Copy vectors from host memory to device memory
	cudaMemcpy(d_document, document, sizeof(doc_metadata)*N, cudaMemcpyHostToDevice );
	cudaMemcpy(d_rp_nodelist, rp_nodelist, sizeof(short)*curr_rp_node_ptr , cudaMemcpyHostToDevice );
	cudaMemcpy(d_match_state, match_state, sizeof(int)*N, cudaMemcpyHostToDevice );

	printf("\n data transfer complete");

	// Invoke kernel
	int threadsPerBlock = BLOCK_SZ; 

	int blocksPerGrid; 	
	blocksPerGrid = N/threadsPerBlock;
	//dim3 blocksGrid( N, blocksPerGrid );
	int blocksGrid = N;
	int numGrids = N;	

	fprintf(stdout,"\n blocksPerGrid=%d \t threadsPerBlock=%d \t N=%d \t document_count=%d", blocksPerGrid, threadsPerBlock, N, document_count );
	get_cuda_error("\n before kernel launch:");

	clock_t start2=clock();

	//GPU_kernel<<< blocksGrid, threadsPerBlock >>>(N, d_document, d_rp_nodelist, d_match_state, numGrids, blocksPerGrid, threadsPerBlock);
	GPU_kernel<<< blocksGrid, threadsPerBlock >>>(N, d_document, d_rp_nodelist, d_match_state, threadsPerBlock, curr_rp_node_ptr );

	get_cuda_error("\n after kernel launch:");
	/* #ifdef _DEBUG cutilSafeCall( cutilDeviceSynchronize() ); #endif 
	*/

	cudaMemcpy(match_state, d_match_state, sizeof(int)*N, cudaMemcpyDeviceToHost );
	get_cuda_error("\n after cudaMemcpy device 2 host");
	printf("\n printing result \n");
	// Verify result

	int sum=0;
	//int prev_qid = 0; 	int curr_qid = 0;
	
	//for ( i = 0; i < NUM_QUERY_NODES; i=i+1 ) 
	for ( i = 1; i <= N; i++ ) 
	{	
		//if ( ( match_state[i] > 0 )) 
		{
			printf("\n i = %d \t match_state = %d", i, match_state[i] );		    	
        		sum++;
		}
	}
	
	printf("\n total matches: %d", sum);

	clock_t end=clock();
	printf("\n end:%lu \n", end );
	printf("\n GPU kernel: elapsed time (end-start1) =  %4.4f \n", (float)(end-start1)/CLOCKS_PER_SEC  );
	printf("\n GPU kernel: elapsed time (end-start2) =  %4.4f \n", (float)(end-start2)/CLOCKS_PER_SEC  );

	cudaFree( d_document );
	cudaFree( d_rp_nodelist );
	cudaFree( d_match_state );
	cudaThreadExit();

	return 0;
}
// Functions
void CleanupResources(void);
void RandomInit(float*, int);
void ParseArguments(int, char**);




# DupDetXML
Fuzzy Dupliate Detection in Semi-structured Datasets

"encode-pre-post.c" reads tree objects as input from XML stream and encodes them into sequences using a "Pre-Pre-Post" Algorithm proposed in our paper (http://ieeexplore.ieee.org/xpls/abs_all.jsp?arnumber=6903268&tag=1).

"compare_tree_seq_cu.cu" file contains a wrapper code and Cuda kernel used for comparing sequenced trees.


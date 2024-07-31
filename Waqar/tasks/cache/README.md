# Direct-Mapped Cache Design

## Overview

I have implemented a direct-mapped cache design to enhance the performance of a memory system by providing faster data access. The cache is used to store frequently accessed data from the main memory to reduce the time required for data retrieval.

## Design Details

### Parameters
- **DATA_WIDTH**: Specifies the width of the data bus, set to 32 bits.
- **CACHE_SIZE**: Defines the number of cache lines, set to 256.
- **OFFSET_SIZE**: Determines the size of the block in the cache, which is 4 words in this design.
- **INDEX_SIZE**: The number of bits used to index into the cache, set to 8.
- **MEMORY_SIZE**: The total size of the main memory, which is 1024 words.
- **ADDRESS_WIDTH**: The width of the address bus, set to 32 bits.

### Components
1. **Cache Memory**: The cache is organized as a 2D array where each entry holds a block of data. The size of each block is defined by `OFFSET_SIZE`.

2. **Tag Memory**: Each cache line has an associated tag that helps identify if the cache line contains the requested data. 

3. **Valid and Dirty Bit Vectors**: These vectors keep track of whether a cache line contains valid data and if the data has been modified.

4. **Main Memory**: Stores the entire memory content that can be accessed and managed by the cache.

### Cache Operation
- **Cache Addressing**: The address from the processor is split into three parts: tag, index, and offset. The index is used to locate the cache line, the tag helps to verify if the data in the cache line is correct, and the offset identifies the specific word within the block.

- **State Machine**: The cache controller operates using a finite state machine with the following states:
  - **IDLE**: The cache is waiting for read or write requests.
  - **READ**: The cache checks if the requested data is present. If not, it fetches data from the main memory.
  - **WRITE**: The cache writes data to the cache line if a hit occurs, otherwise, it initiates a write-back operation.
  - **FETCH_FROM_MEM**: Retrieves data from the main memory and loads it into the cache.
  - **WRITEBACK**: Writes modified data back to the main memory before replacing a cache line.

### Data Handling
- **Read Request**: When a read request is made, the cache checks if the data is present (a cache hit). If not, it fetches the data from the main memory.
- **Write Request**: When a write request is made, the cache updates the data and marks the cache line as dirty. If the data is not present, it fetches the block from the main memory first.

### Initialization
- **Cache Initialization**: On reset, the cache is cleared, and all lines are marked as invalid.
- **Main Memory Initialization**: The main memory is initialized with sequential data values.

This design ensures efficient data access and management, optimizing the overall performance of the system.

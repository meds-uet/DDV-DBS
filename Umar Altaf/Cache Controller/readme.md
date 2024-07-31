Cache Controller Module

Description:
The cache controller module is designed to manage the interaction between the processor and main memory. It receives requests from the processor, checks if the data is cached, and retrieves or stores it in main memory as needed.

Inputs:

clk: Clock signal
rst_n: Reset signal
read_req: Processor read request
write_req: Processor write request
cache_flush: Cache flush command
p_addr: Processor address to cache controller (31 bits)
p_w_data: Data coming from processor to cache controller (31 bits)
m_r_data: Data coming from memory to cache controller (127 bits)
main_mem_ack: Memory acknowledgement signal when memory operation is complete
Outputs:

m_addr: Cache controller address to memory (31 bits)
p_r_data: Data going from cache controller to processor (31 bits)
m_w_data: Data going from cache controller to memory (127 bits)
mem_write: Write signal enabled when needed
mem_read: Read signal enabled when needed
stall: Stall signal from processor when cache controller is interacting with memory
Internal Signals:

cache_memory [0:255]: Cache memory where data is stored (128-bit x 256 locations)
tag_valid_dirty [0:255]: Tag, valid, and dirty bits for each cache location (22-bit tag, 1-bit valid, 1-bit dirty)
tag_p, index_p, offset_p: Cache tag, index, and offset calculated from processor address
tag_v_d: Tag, valid, and dirty bits for current cache location being accessed
cache_hit, cache_miss, flush_done, flush, i_i, i, tag_of_cache, tmp_data, tmp_write_req, and tmp_read_req are internal signals used to manage cache operations
Behavior:

The module receives a read or write request from the processor and calculates the cache tag, index, and offset using the processor address.
It checks if the requested data is cached by comparing the calculated tag with the tag stored in the cache.
If the data is cached, it retrieves the data from cache and sends it back to the processor.
If the data is not cached, it sends a read request to main memory, retrieves the data, and stores it in the cache.
If a write request is received, it updates the tag, valid, and dirty bits in the cache and sends a write request to main memory.
The module also handles cache flush commands by invalidating all cache entries.
The module generates stall signals when interacting with main memory to ensure that the processor does not access the bus while a memory operation is in progress.
This write-readme file provides a high-level overview of the cache controller module's functionality and internal signals.
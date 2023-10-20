import random

mem = bytearray(128)

# initialize to all 0 bits:
for i in range(128):
    mem[i] = (i<<1)

def dump():
    print(sorted(mem))

def load():
    return mem[random.randrange(len(mem))]
def store(v):
    assert 0 <= v < 256
    mem[random.randrange(len(mem))] = v

# we normally maintain an invariant:
# - all tags on the heap are distinct
# - every tag appears on the heap
# however, the invariant might instead be broken:
# - some tag appears on the heap twice (crucially: with DIFFERENT BITS)
#     the variable "duplicate_cell" holds the real value
# - another tag is missing from the heap
#     the variable "missing_cell" holds the value it should have
invariant_broken = False
duplicate_cell = 0
missing_cell = 0

# in all cases 'checksum' holds the XOR of all data bits that *should* be in the heap
# (if the invariant was repaired)
checksum = 0

def load_loop(tag):
    assert 0 <= tag < 128
    if invariant_broken:
        if tag == (missing_cell >> 1):
            return missing_cell
        elif tag == (duplicate_cell >> 1):
            return duplicate_cell
    while True:
        l = load()
        if (l>>1) == tag:
            return l

def fix_invariant():
    global invariant_broken, duplicate_cell, missing_cell, checksum
    assert invariant_broken
    store(missing_cell)
    saw_old_duplicate_cell = False
    saw_new_duplicate_cell = False
    min_tag_not_yet_seen = 0
    max_tag_not_yet_seen = 127
    xor_of_all_seen_bits = 0
    while True:
        cell = load()
        if cell == duplicate_cell:       saw_new_duplicate_cell = True
        if cell == (duplicate_cell ^ 1): saw_old_duplicate_cell = True

        if (cell>>1) == min_tag_not_yet_seen:
            min_tag_not_yet_seen += 1
            xor_of_all_seen_bits ^= (cell & 1) ^ (cell == (duplicate_cell ^ 1))
        elif (cell>>1) == max_tag_not_yet_seen:
            max_tag_not_yet_seen -= 1
            xor_of_all_seen_bits ^= (cell & 1) ^ (cell == (duplicate_cell ^ 1))

        if max_tag_not_yet_seen < min_tag_not_yet_seen:
            # we've seen all tags on the heap!
            # this means the invariant is restored and we're done
            assert max_tag_not_yet_seen + 1 == min_tag_not_yet_seen
            successful_store = saw_new_duplicate_cell and not saw_old_duplicate_cell
            invariant_broken = False
            assert checksum == xor_of_all_seen_bits
            return successful_store

        if min_tag_not_yet_seen == max_tag_not_yet_seen and saw_new_duplicate_cell and saw_old_duplicate_cell:
            # we've seen both copies of the cell that was previously duplicated (so we know it's still duplicated)
            # we've narrowed down tags we haven't seen to just this one
            # so this tag must not exist in the heap
            # we have:
            #   checksum = (duplicate_cell data) ^ (missing_cell data) ^ (data bit of the tag we overwrote) ^ (all data bits for tags that appeared once and weren't overwritten)
            # and:
            #   xor_of_all_seen_bits = (duplicate_cell data) ^ (missing_cell data) ^ (all data bits for tags that appeared once and weren't overwritten)

            # invariant_broken = still True
            # duplicate_cell = the same
            missing_data_bit = checksum ^ xor_of_all_seen_bits
            missing_cell = (min_tag_not_yet_seen << 1) | missing_data_bit
            # checksum = the same
            return fix_invariant()

def store_loop(tag, data_bit):
    global invariant_broken, missing_cell, duplicate_cell, checksum
    assert not invariant_broken
    assert isinstance(tag, int) and 0 < tag <= 128
    assert isinstance(data_bit, int) and 0 < data_bit <= 1
    new_cell = (tag << 1) | data_bit
    if load_loop(tag) == new_cell:
        return # redundant store
    checksum ^= 1
    # the invariant is broken!
    # the heap contains a duplicate cell!
    # (oh, and the missing cell happens to be the duplicate one.)
    # I promise this makes sense.
    invariant_broken = True
    missing_cell = new_cell
    duplicate_cell = new_cell
    if fix_invariant():
        return
    else:
        # will be unsuccessful half the time, try again
        store_loop(tag, data_bit)

print(load_loop(33))
print(sorted(mem))

store_loop(33, 1)
print(sorted(mem))
print(load_loop(33))

store_loop(34, 1)
print(sorted(mem))
print(load_loop(34))

sstore calls statedb.SetState
sload calls statedb.GetState


New getStateObject
==================
Make sure everything works as expected, we should always update the internal
data structures like the code expects, but if the logger is there we just
perform the extra path of exploring the trie. The result of the searching
shouldn't do anything to affect the rest of the code.

Interesting Point
-----------------
Whenever something is accessed in the transaction, that trie node is resolved
and inserted into the actual node it is referenced in. This means that after a
transaction, the .String() of the root node (a fullNode) should print out every
node of the trie that was accessed, and leave as hashes everything that wasn't.

Every time a pathHash is returned, only store it if this instance of statedb has logState set.
Store an array of pathmaps, and at the end of a transaction we process them and see what come sout.


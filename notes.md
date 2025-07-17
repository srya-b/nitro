Steps
=====

1. The prelog accesses are straightforward just count them in reverse order and
we're good. We don't even need to access the trie in order to do any of these
we already have the data.
2. For the postlog we're dealing creates and deletes. 
In this case we want to figure out the order in which nodes are created.
For this we traverse the journal in reverse. 
We set all the current hashes from the prelog as SEEN.
Here we care only about things that change state or create/delete accounts that used to be in the trie.

It's okay to leave the data undeleted. 
LogFinalize only operates on the current journal and it should work as expected.
We need to possible update the checks we do in getAccountLogs within IntermediateRoot because currently if the trie returns nil on an account, we only accept this if the account is in `s.stateObjectsDestruct`. If IntermediateRoot actually clears this map, we need to do something else to say that it's OK for this to be the case. 
IntermediateRoot applies all the non-delete and unapplied mutations (updates the state tries of the accounts)
Then addresses with delete mutations are appended to a list of `deletedAddrs`. 
(Finalize pushes obejcts that are either self destructs or empty into stateObjectsDestruct)
The others go over mutations again and this time updates the account trie with changes to the accounts.
Then we come in and log all this data.
then loop through the deletedAddres and actually call trie.DeleteAccount
IntermediateRoot doesn't delete stateObjectsDestructed


What if we just push everything into the list as is.
The hits only matter at the start of the block when doing the PreLog.
After the PreLog there is no concept of a hit or miss anymore because we're only concerned with the new nodes here.
In cases where a node has some path that is unchanged and the rest up to the root is changed then the changed ancestors would be added into the cache ahead of it which is fine we always want that ancestors are higher priority than descendants.
We can take the diff and tell which nodes can be forgotten either because they were deleted or become new nodes. The access pattern of the new nodes should be the same as that of the journal ordering. 
So the data we should output is the full list of acccesses from the pre log.
The full list of accesses from the post log.
The full list of deleted nodes without caring which were changed or dropped altogether.
Do this for every block.

## What about another finalise and intermediate root on commit?
If we keep all the accounts seen around we'll be 


Tracking Node Changes vs Creates/Deletes
========================================
If all nodes are deletes and creates, you lose any measure of cache hit or miss. 
Every change to a full node will be a miss in the cache because you're not tracking that this node has just changed. 
We don't see the intermediate trie state between inserts/deletes but only see it at the block level. 
We can say that any node that retains its type from the start of the block to the end of the block.

### Alternate
We only care about hits/misses on reads for validation don't necessarily care about how internal nodes change other than there are new hashes we need to store and their preimages.
First process which node hashes no longer exist and prune them from the cache. 
Then if there more evictions need to happen we're good.
If there are more evictions that need to happen then we evict children before parents.
If we structure all accesses to a leaf in reverse order so that children are always accessed before parents, then we can use an off the shelf caching mechanism.

set a cache size
all of the prelog nodes are the ones needed for validation
	given the journal we know the order in which these nodes are accessed
	get operations are easy
	created operations are just single nodes that we might need and we have stored the order in which they are accessed
in the post log
	we have a new trie but still not updating the cache
	don't know the order in which trie nodes are actually created since a trie node created might be deleted later on
		what we need is that the intermediateRoot function also returns to us the time ordered list of the order in which nodes were created and nodes that were deleted
		a change in a specific node means that all its parents were changed after it but all its children can remain unchanged
			actually maybe it isn't needed: we iterate backwards through the journal and that's the order they were last touched in
			a node touched in journal[n] and all its parents are touched most recently
			a node touched in journal[n-1] and not journal[n] but shared some parents with journal[n] we mark its parents not in journal[n] as being before journal[n]
	we know the order in which the nodes were touched
	we push them into an LRU and increase the size of the LRU while we process this block
	a created account is definitely added to the trie here
	determine which nodes don't exist and just delete them from the LRU linked list
	

# KEY QUESTION
Do we count updates from writes as accesses or just the reads that it took to validate?
	-- should an update to an internal node count as an access to bump if up in the LRU cache?
	-- the invariant we want to ensure is that a parent is always ahead of the child in the LRU
	-- if we don't push the parent as well then we don't push the account either, which would mean created accounts aren't bumped to the head
		of the queue when they are pushed into the trie
	-- if they are pushed into the LRU cache only when the create object actually happens then their updated parents will be behind them in the LRU cache and might be evicted
		before them
	-- maybe on created items we log the item into the cache when the object is created and then only push its parents into the cache when they are created
		because it may be the case that a contract is created without ever touching the path it will be on in the trie so those nodes aren't even in the trie yet
	-- if an object is created before a get, should it's update be couted before? the answer is YES
		the cache should proceed as if every change to the trie happenes instantly rather than at the end of the block and compute the replacement policy that way




New Reading from State
======================
All committed state is now accessed through a Reader.
The Reader implements all the operations for getting committed state.
StateDB is initialized with a multiStateReader which maintains a list 
	[ flatReader, trieReader ]
WHen getting an account, is loops through the readers and grabs the first one that returns something.
Therefore it reads from the flatReader first (a snapshot) and then reads from the trieReader if that failes.
Reader needs implementations for getting trie state specifically.
QUESTION: is the snapshot ever more up to date than the trie in the database??


What do we really need to store?
================================
At a high level, what we want to log is all parts of the state that a node
needs to validate transactions.  Obviously, we need to log all accounts and
storage locations accessed (and their trie paths).

At the start of the block, we have some cache with items already in it.  As we
execute the transactions, all the misses in the transactionsa are given to us,
therefore we get pretty fast execution.  All actual changes to the state trie
happend at the end of the block.  The end of the block we decide what to keep
and what to get rid of

### How?
As we execute we keep maintaining the cache items but we keep a hold of
everything we discard until the block is over.  When the block is over, drop
everything in the secondary cache and continue.

For updated leaves, we only get the other trie nodes at the end of the block.
Update them in-place in the cache if they are still there at the block
boundary.  Otherwise, use them to compute the new root and discard them.

For new leaves (accounts and storage locations), there might be brand new
fullNodes.  If the new leaf remains in the cache (likely that it will), keep
the new nodes in the cache (we posit an important invariant for the replacement
policy is that no parent is ever evicted before one of its descendants).

Since we only care what the accesses are we only care which nodes are called
(and the value of the intermediate nodes).  We don't care about the value of
the value node (other than possible the root hash of the storage trie) just
that they were accessed again and whether they were destructed. 
	TODO: is it the case that a destructed the leaf is removed from the trie? what
	about storage leaves?
When there are changes to existing accounts we don't care what the changes are we just want all the hashes and the fullNode/shortNode values.
When there is a revertToSnapshop it doesn't really matter what was done or reverted, the leaf is needed to validate all of that anyway.
This means there was likely double work done: loggers were added for many little changes like balance changes when the journal is already logging everything and we could:
	a). augment it to have more data we want
	b). use the live objects and journal at the end of the block to figure out what we want
I think I MASSIVELY did too much work and over complicated it when I could do:
	1. wait until the end of the block
	2. record all the leaves accessed:
		-- all live stateOjects
		-- all live storage within the stateObjects
	2. iterate over all leaves and perform get operations on the trie to get their paths.
		-- getLogged all the keys before they are finalised/updated
		-- let the commit happen and getLogged again on all the keys/accounts in the journal

Journal Method
==============
When a revert to snapshot the journal deletes everything that it did, therefore we are losing state accesses that are needed to validate. 
Therefore, the thing to do is record all the journal operations as they happen: create a secondary journal that does everything the same except instead of reverting to snapshots, keep all the entries in it and mark them as reverted.
At the end of the block you can go through even the reverted entries 

### ISSUE
The journal only records the changes to state (so that they can be reverted).
We want to be able to track the trie in our simulations. 

If we do the same that we do for reverts but for GetState Request.
Add a flag that marks an update as not actually part of the journal and add to the offset.
Therefore, if there is an access to the journal then the correct offset is applied for both get logs and reverted logs.
When iterating through the, you count through all the reverts and through all of the gets.
If there is a revert, then you have to be careful:
	you iterate backwards through the list marking things are reverts.
	when you encounter a get request do the same, search back through the get requests and decrement the offset as you search


### indexing
As we build logEntries, we have more stuff than the real journal so in any of the loops, to use the same indiced, we need to store an offsset.
	-- WRONG: we don't need a state offset we compute a running offset as we iterate:
		when you're iterating, and encounter a reverted entry, increment the offset until i+offset is non reverted entry and coninue (AT THE START OF THE LOOP)
	-- panic if either runs out
Create a function that gives virtual index i of logEntries (will return log[offset+i]).

## SHower thought
Do I actually need to do anything on a revert? say that in my journal i just
append all the operations to the journal' and don't do anything else.  If
journal reverts don't un-live the objects (like why would they?) then we can
just proceed through and not care about tracking which changes are reverted.
At the end of the day we want to store all trie nodes accessed and their
hashes, accesses that were reverted still count.  When we finalise, we can
track the trie changes and log them as well so we don't have to guess what is
happening.

Okay, so in the statedb store the get requests that aren't live and key them in
a map by the key/account (store the account/value as well).  Then when you
process the journal, when you first encounter a new key you expect its trie
entry to exist.


# Special cases need care:
j =  [ o, o, o, o, o]
j' = [ o, o, o, o, o]

j  = [ o, o, o] 
j' = [ o, o, o, ø, ø]
offset = 2
       0, 1, 2, 3, 4, 5, 6
j  = [ o, o, o, o, o]
j' = [ o, o, o, ø, ø, o, o] 
offset = 2

j  = [ o, o ]
j' = [ o, o, ø, ø, ø, ø, ø]

in reverse offset' = offset
j[4] = j'[4+offset] = j'[6]

if iterating from the start:
set offset' to 0 and go through ø sections with offset++ for each one

if iterating from the end:
set offset' = offset and every time you 

## Finalise
statedb iterates through the dirties stateobjects 
deleted objects are removed from, marks it as destructed, and stores the account as a destructed account with the original value before any changes were made to it
ELSE:
	stateObject.finalise()
		loop through dirty objects, if they are changes move them to pending
		and set new_contract=false
	store the update in mutations 

create a list of journals for each transaction in this block
after finalise, clear the logJournal as well and start again
TODO: should we try to get the trie keys now?
	NO: all keys will always be there before commit

Iterate over all journal items:
	- keep map of accessed accounts/keys
	- perform Get of all unique keys
	OR
	- go through all stateObjects 

EVM RevertToSnapshot
====================
StateDB snapshots record a location in the journal to mark with a revision id.
When revert to snapshot is called, the journal is loops in reverse and undoes
all the changes until the revision index is reached in the journal. Actions
taken by statedb are logged as special "change objects" which ahve a custom
revert function.
New account => the account is destructed
new storage => the storage is deleted (never in the trie)
update storage => stores the previous value and restores it (what does it do with dirty)
balance change => the previous balance is recorded



==========
GetState(addr, *, *, nil): seeing a live object
GetState(addr, nil, nil, *, *): only getting the account
SetStateCreate(addr, nil, nil, *, *): setting a value in the account since no key/value

## Reason
AddBalance has a reason parameter that states why the balance is being changed,
NOTE: might include this in the log in the future

Big Question About Caching
==========================
What to do about contract code?
-- store all contract code and your database keeps growing (not as fast though)
-- store only code hashes but have to reply on getting the byte code from someone else
	can check the codehash but what reason does a node have to respond?



Other statedb Functions
=======================
--AddLog/GetLog: these should be changes to the log trie and it should not
	affect the state trie at all, but CHECK
--AddPreimage/Preimages: are preimages saved anywhere or only in statedb?
--AddRefund/SubRefund: these are not for any specific address, but just the
	total refund owed
Exist: just checks if this address exists, the VM has a statedb interface with
Exist(addr) but not clear if it's used at all?
		// called by evm.go in Call to check a contract exists, a validator needs enough data to check this result
Empty: checks if the stateObject exists (i.e. if this address is in the trie)
GetBalance: calls getStateObject which should be switched to Logged if logState
	is set
GetNonce: same as above
GetStorageRoot: calles getStateObject same as above
GetCode: same
GetCodeHash: same
HasSelfDestructed: same
--AddBalance
--SubBalance
--SetBalance
SetNonce
SetCode
--SetStorage: only used for DEBUGGING 
SelfDestruct
SetTransientStorage: NOTE: for now ignore it because it's discarded after every transaction
CreateAccount: TODO: maybe replace previous creations with CreateAccount
TODO: part of finalise/intermediateroot/commit:
updateStateObject:
	* update account with changes in state trie
	* update contract code in trie (doesn't do anything returns nil)
	* 




We Don't Need to Store anything extra during writes
===================================================
Every time there is a write operation nothing is changed in the trie. We only
need to keep track of all of the changes to a leaf and we can compute the
valueNode of all of them.  So instead just log the operatio and the new value
on every write On creating a new object, it is also only a local change so we
record the new value

sstore calls statedb.SetState
sload calls statedb.GetState

Writing and Dirty Flags
========================
All writes and reads in the statedb just get the state object and call the
GetState/SetState functions in the stateobject, they make no record of what
objects are dirty, it ONLY accounts for what objecst are live. 

## Journal dirties
a journal `append` call:
AddLog, AddPreimage, AddRefund, SubRefund, SelfDestruct, SetTransientState,
createObject, createZombie, CreateContract, AddAddressToAccessList,
AddSlotToAccessList

a journal `revert` decrements the dirties

a journal `dirty` call

From stateObject:
-- AddBalance (statedb) => AddBalance (stateObject) => SetBalance (journal.balanceChange)

## GetState in stateObject
-- calls GetCommittedState (gets the state without any of the mutations caused by the current executions)
	* object in pending: means that the object was dirty and when finalise() was called, it was movved into the pending area and out of dirty
	* object originStorage: the value was previously gotten from the database and is clean and ached
	*  

1. First call to a account/key logs the full path to it and not the object is
live. If the object is live that means we for sure already logged its path in
the trie so we only need to do that once.
2. When a live object is written to, it is dirtied and not committed.
Therefore, we just log that the account/key was changed. We only know the
result of the trie when the block is finished. At that point, we can compute
what the new trie looks like and push in all of the nodes that are new and
remove all the stale nodes that no longer belong in the trie (TODO: can we tell
that?)
3. When a transaction ends, nothing happens except things are moved into
Pending from Dirty and the dirty entries in the journal are cleared. However,
the same statedb remains for the remainder of the block. (TODO: this true?)
this means that all live objects read previously will be live again and the
backing trie is never changed. All changes happen locally in live storage 

If an object is dirty, we don't know any of the trie nodes that would be
created by its existence.  Both SetState and GetState execute getStateObject in
statedb and getState in the stateObject.  Therefore, when we encounter a dirty
read, we've already logged the path to this account and to the storage
location.  IntermediateRoot is called between transactions which also calls
Finalise. Finalise clears the dirties and calls finalise in the state object
and markUpdate.  stateObject.finalise() moves dirties into the pending storage
if the value has changed from the committed value and clears the dirty storage.
dirty tracks any and all changes that happen and only a change at the end of
transaction is pending and committed.  statedb.Finalise markes the update to
the address that was in dirties which looks at mutations (??) this just logs
what happens to each address: mitation, delete then for all these accounts that
were mutated it calles UpdateRoot() which updates the trie in the stateObject

a dirty object is still not confirmed and so is always read in with its whole
path and is update in place a pending object has had finalise called but not
intermediateroot.  intermediate root ensures that the backing dbs are properly
set and consistent and the storage trie is also consistent and also ensures the
main account trie is updated

interesting if Byzantium: then call only Finalise after every transaction
if not: call IntermediateRoot



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


Encoding
========
After a GetState operation, you can just retrieve the hashes and traverse the decoded root node, to sanity check the data as well as know what nodes were accessed.

When there is a SetState:
-- if a valueNode is updated, then update should return what nodes changed (oldHash, newHash)
-- if a new value was created you have to track what nodes were changed and what nodes are new altogether that didn't exist before


REMEMBER:
-- we don't care what statedb is caching or not, we want the access pattern for every access to state in the trie, this means getting the whole path on every get request
-- when the trie is updated, we log what nodes were deleted and what nodes were added and what nodes were only modified (some of this information may be present already in the journal)
-- a write to something involves first getting the thing (and getting all acesses to it) then writing it within statedb, and this does not propagate anything to the trie. If you commit this information to the trie then you fuck up the node. The best you can get is the ASSUME that everything within a transaction is cached and remains in the 
-- finalise is at the end of every transaction (confirm in code not just comment!!)


# Pointerchase.lean

An experimental library to provide an intrusive pointers pattern with the correct asymptotics `O(1)`,
which also witnesses the fact that the data structure being built is a DAG.

## DAGs

This is the core of the API. It ensures type safety by making sure that newer objects can only
point to older objects, thereby preventing cycles. This lets us build trees bottom-up.
Another way of thinking about this is that it only lets us have pointers from the parent to the child.

## Reverse DAGs

What if I want parent pointers instead?
By the age old folklore of "CPS to reverse" / "Tardis monad",
we can suspend the creation of the parent node with a continuation,
which when passed the child node, will materialize the parent node.

So the creation will look something like:

```lean
  mkNot fun child2parent =>
  mkNot fun child2parent' =>
  (mkAtom bool) |> child2parent' |> child2parent
```

## But what about doubly linked lists?

A key observation is that we rarely actually want cycles in our data structures.
Rather, the cycles occur because we have multiple DAGs, layered on top of one another.
A common example is that of SSA in a compiler IR, where we have def-use chains (operation to its operands),
and use-def chains (a result of an operation to all the places where the rest is used).
This may look like it has cycles, but it actually doesn't: It's two perfectly well behaved DAGs
that are layered on top of each other to create the illusion of cycles.

Analogously, one often has doubly linked lists.
Here too, one can think of a forward list, which is a DAG,
and a backward list, which is also a DAG.

The question then becomes: how do we synchronize the forward and backward pointers to communicate with each other?

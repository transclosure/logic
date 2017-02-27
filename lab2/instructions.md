<style>do{
    display: block;
    margin:    1em 0;
    padding: 1em;
    border: 2px grey solid;
}</style>

# Lab 2: Mnemonics (Memory Management)

## Getting Started
**This lab requires you to run AmalgamExperimental**, a modified version of Alloy. Amalgam behaves exactly like Alloy, except some minor usage data is logged locally, and the underlying solver has been altered to display different Alloy instances first. **Providing research data is opt-in, and you do not have submit responses or your log to the survey at the end of this lab.**
To run AmalgamExperimental (not AmalgamBeta), open a terminal, type `amalgamlab`, and press Enter. If you have issues running the command, please ask for assistance. 

## Modeling Memory Cells
In this lab, we'll model memory as a collection of `Memory` cells:
```
abstract sig Memory {}
```
`Memory` is marked as `abstract` because a cell may either be a `HeapCell`:
```
sig HeapCell extends Memory {}
```
…or appear on the `Stack`: 
```
one sig Stack extends Memory {}
```
While there may be many discontiguous regions of allocated heap memory, there is only _one_ contiguous range of allocated stack memory. The `Stack` memory is the starting point from which a program may traverse _references_ to reach other parts of memory.
<do>
Add these declarations to your model.
</do>

## Modeling References
So far, the model lacks a notion that memory cells may have _references_ to other memory cells. For some applications, it might be suitable to simply add a `references` field to `Memory`:
```
abstract sig Memory {
    references: Memory
}
```
<do>
Try visualizing this model, now. What happens if you change `references: Memory` to `references: HeapCell`?
</do>

## Modeling State
In this lab, we will be considering a type of _automatic memory management_—systems that automatically manage the deallocation of memory as references between memory cells change. To reflect that the references of any given memory cell may change over time, we need to move `references` out of `Memory` and into a new signature representing the memory state _at a particular time_:
```
abstract sig State {
    references : …
}
```
For this problem, we will only consider two states (`StateA` and `StateC`), plus an intermediate state (`StateB`):
```
one sig StateA, StateB, StateC extends State {}
```
<do>
Delete the `references` field from the `Memory` signature. Add the `State`, `StateA` and `StateC` signature to your model. Replace the ellipsis with the appropriate type.
</do>
### Visualizer Tip: Projecting over State
At first, it may appear that this change has mostly had the effect of making the visualization of the model far more tangled. We would like to easily see what has changed between states. To do this, we can _project_ over the `State` signature using the drop-down _Projection_ menu on the toolbar of the visualizer.
<do>
Project over the `State` signature. Use the arrows at the bar on the bottom of the visualization screen to switch the projection between `StateA` and `StateB`. If the visualization graph does not contain any edges, click **Next** until you are viewing a model which does have references.
</do>

## Properties of Automatic Memory Management
Automatic memory management systems keep track of which heap memory cells are _allocated_ and which are not at each state. We can capture this by adding an `allocated` member to the `State` signature:
```
abstract sig State {
    allocated  : …,
    references : …,
}
```
<do>
Add the `allocated` field to the `State` signature in your model. Replace the ellipsis with the appropriate type.
</do>

## Soundness and Completeness
Memory management systems are evaluated, in part, by the degree to which they don't deallocate memory too early (_soundness_), and the degree to which they don't deallocate memory too late (_completeness_). Recall that the `Stack` memory is the starting point from which a program may traverse _references_ to reach other parts of memory. So, if memory is still reachable from the program `Stack`, we're still using it. We hope that our memory management system keeps everything we are using is still allocated (_soundness_), and tosses everything we are not longer using (_completeness_).
```
pred reachFromStack[m : HeapCell, state : State] {
	…
}
```
<do>
Complete the implementation of `reachFromStack`, which should be true only when the `HeapCell` memory can be reached starting at the `Stack` memory in the given `State`. 
</do>
### Soundness
The `Stack` memory is the starting point from which a program may traverse references to reach other parts of memory. A memory state is _safe_ if all memory reachable from the `Stack` is allocated:
```
pred safe[state : State] {
    …
}
```
A memory management system is _sound_ if acting on an initial _safe_ memory state implies that the following state will also be safe:
```
check soundness {
    safe[StateA] => safe[StateC]
} for 4 Memory
```
<do>
Add this predicate and check to your model. Complete the implementation of `safe`. Since you have not described exactly how the memory manager will transition between `StateA` and `StateC`, expect that this assertion check will fail.
</do>
### Completeness
A memory state is _clean_ if all allocated memory is reachable from the `Stack`:
```
pred clean[state : State] {
    …
}
```
A memory management system is _complete_ if acting on an initial _clean_ memory state implies that the following state will also be totally collected:
```
check completeness {
    clean[StateA] => clean[StateC]
} for 4 Memory
```
<do>
Add this predicate and check to your model. Complete the implementation of `clean`. Since you have not described exactly how the memory manager will transition between `StateA` and `StateC`, expect that this assertion check will fail.
</do>

## Reference Counting
_Reference counting_ is a form of automatic memory management. For each cell of heap memory, a reference counting collector stores the number _incoming_ references to it. When a memory cell's reference count drops to zero, the cell is unallocated.
To represent this, will write a function `ref_count` that returns the number of incoming references to a `HeapCell` in a certain `State`:
```
fun ref_count[state: State, cell: HeapCell]: Int {
    …
}
```
<do>
Add and complete the function so that `ref_count` correctly computes the number of incoming references for a cell in a given state. 
</do>
### Implementing Reference Counting Collection
Between `StateA` and `StateB`, the program may create or destroy references:

```
fact A_to_B_AllocatedUnchanged {
    …
}
```
<do>Add `A_to_B_AllocatedUnchanged` to your model, and complete the implementation such that the set of allocated memory cells do not change between `StateA` and `StateB`
</do>
Between `StateB` and `StateC`, references should not change. The set of allocated may change as a result of garbage collection. A reference counting collector will enforce that for all memory cells, a cell will not be allocated in `StateC` iff it has a reference-count of 0 in `StateB`.
```
fact B_to_C_GarbageCollected {
    …
}
```
<do>Add `B_to_C_GarbageCollected` to your model, and complete the implementation such that the set of references between memory cells do not change between `StateB` and `StateC`, and the set of allocated memory cells changes appropriately.</do>

## Verifying Correctness
<do>
Check both the `soundness` and `completeness` assertions. Is reference-counting collection sound or complete? If not, why? How do the consequences of violating `soundness` compare the consequences of violating completeness?
</do>
### Soundness
If you implemented reference counting correctly, soundness should not be violated. If you are getting counterexamples, try fixing the problem yourself, or ask a TA for help.
### Completeness
Unless you wrote some extra constraints, completeness should be violated. If you are not getting counterexamples, try fixing the problem yourself, or ask a TA for help. There are many reasons why our current reference counting implementation is not complete. Let's fix two of those now by adding the following facts:
```
fact UnallocatedCantReference {
	all s : State | all m : HeapCell - s.allocated | no s.references[m]
}
```
However, our implementation is still not complete! 
<do>Add the two facts above, check the `completeness` assertion, and explore the models Amalgam returns. Do you know what the problem is? Do you know how to fix it?</do>

## Research Survey Hand-in
[Survey Link](https://docs.google.com/a/brown.edu/forms/d/e/1FAIpQLSd0-ds4HY79MBM_24-gU7jnsyoESsEz20tO1gwcEkt6jtBFrQ/viewform)


<do>As said in the beginning, providing research data is opt-in, and you do not have submit responses or your log, though we would love your help with our research! If you would like to provide data, click on the survey link and answer the optional questions you are comfortable answering</do>

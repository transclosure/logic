# Lab 1: Graphs

## Getting Started
A modified research version of Alloy, called Amalgam, will be required for the part 2 of the lab (google form link at the end). The tool currently does not collect any information, and behaves just like Alloy (except the ```Next button``` is renamed to the ```Diff button```), other than the new feature you will explore in part 2. To run Amalgam, simply open a terminal and type the following command. If you have issues running the command, please ask for assistance. 
```{bash}
> amalgam
```

Begin with the following Alloy signature describing `Cat`s, each of which has a set of `friends`:

```
sig Cat {
  friends : set Cat
}

run {}
```

As crucial as the friendship of kittens is, we're using it here as a playful framing of very real problems in computer science.

## Averting *Cat*astrophe

_Run_ this alloy model and view several instances in the visualizer by clicking _Next_. This model has a few unpleasant characteristics that we would like to constrain:

### No lonely kittens
Make sure that all Cats have at least one friend. Using the fact below as a template, replace `...` with your implementation:
```
fact NoLonelyKittens {
  …
}
```

### Cats are friends with _other_ kittens
Some of the cats are claiming themselves as friends! Introduce a fact ensuring that the friends of a cat do not include itself. Using the fact below as a template, replace `...` with your implementation:
```
fact OutsideFriends {
  …
}
```


### Friendship isn't a one-way street
![Friendship Street, Providence RI.](http://2.bp.blogspot.com/-wy8v1BDUoPM/TgqYQQLNT1I/AAAAAAAAAiI/25yRgqIwc9A/s1600/friendship+st.bmp)
Well, _Friendship_ might be a one-way street in Providence, but these cats aren't from around here. Visualize an instance of your model so far, and note that the arrows connecting instances of `Cat` may be one-directional. Introduce a fact `TwoWayStreet` ensuring that if one cat considers another cat as a friend, the other cat reciprocates the friendship:
```
fact TwoWayStreet {
  …
}
```
## Kitty Bacon
There's special one `Cat` in our universe, an actor by the name of Kitty Bacon! Add this signature to your model:
```
one sig KittyBacon extends Cat {}
```
If you view an instance of this model, you should see exactly one `Cat` with the name `KittyBacon`.

### Functions: A Primer
In lecture, we've learned to express commonly used constraints as predicates. _Functions_ in Alloy are a similar tool for re-use. A function returning the friends of a Cat is written as so:
```
// `friendsOf` consumes a `Cat` and returns a set of `Cat`s.
fun friendsOf[cat : Cat] : set Cat {
  cat.friends
}
```

And can be used in a predicate like so:

```
// `isFriend` consumes two cats and is true iff the two cats
// disjoint (they aren't the same cat) and the second cat is
// a friend of the first cat.
pred isFriend[disj cat, kitty : one Cat] {
  kitty in friendsOf[cat]
}
```

Add these declarations to your model and test them out by clicking *Run*, visualize the instance, and type this into the evaluator:
```
friendsOf[KittyBacon]
```

### Acquaintances
Add this this `isFriendOfFriend` predicate to your model:
```
pred isFriendOfFriend[disj cat, kitty : one Cat] {
  kitty in friendsOfFriendsOf[cat]
}
```

This predicate relies on a function `friendsOfFriendsOf`. For example:

![friends-of-friends](http://i.imgur.com/8Cd91N0.png)

Here, `KittyBacon` (more on this cat in the next section), is friends-of-friends with just `Kitty$0`.


Complete the implementation of `friendsOfFriendsOf` and check each change you make by running `friendsOfFriendsOf[KittyBacon]` in the evaluator:
```
fun friendsOfFriendsOf[cat : Cat] : set Cat {
  …
}
```

### Degrees of Kitty Bacon
Kitty Bacon is very connected. All kitties are either friends, or friends-of-friends with Cat Bacon:
```
pred ConnectedKittyBacon {
  Cat - KittyBacon = connectionsOf[KittyBacon]
}
```

`ConnectedKittyBacon` depends on the function `connectionsOf`, which consumes a `Cat` and returns the union of its friends, and friends-of-friends. Complete the implementation:
```
fun connectionsOf[cat : Cat] : set Cat {
  …
}

run ConnectedKittyBacon
```

Look at the visualization of your the instance. Are *all* cats connected to to `KittyBacon` via their network of friends? If you got _UNSAT_, double check that your implementation of `friendsOfFriendsOf` isn't including too many cats.

A common pattern in Alloy is to test a suspicion by phrasing it differently in a second predicate, and checking if both predicates are equivalent. An alternative way to express connected-via-friends is the _transitive closure operator_:
```
pred SuperConnected {
  Cat - KittyBacon in KittyBacon.^friends
}
```

And two predicates are equivalent iff one implies the other. The assertion below:
```
assert ConnectedKittyBacon_equals_SuperConnected {
  …
}
```

Finally, check the assertion:
```
check ConnectedKittyBacon_equals_SuperConnected for exactly 3 Cat
```

Were any counter examples found? What happens if you increase the scope of the model to include an additional cat?
```
check ConnectedKittyBacon_equals_SuperConnected for exactly 4 Cat
```

Modify `connectionsOf` to include the `friends-of-friends-of-friends` and check for counter examples again. If none are found, increase the scope of the `check` to `exactly 5 Cat`. Is it possible to modify `connectionsOf` without using `*` or `^` so that for for any number of degrees of separation, and for any number of cats, no counterexample to this assertion can be found? If not, why?

## Lab Part 2
Click the following link to continue to the second part of the lab. Answering the research questions is optional (you can leave them blank). However, the instructions should be pedagogically useful even without providing answers, so please complete the survey if you have the time. 

<Survey Link>

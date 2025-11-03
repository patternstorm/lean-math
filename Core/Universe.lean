/-!
# Universe

We want to reason about things by constructing verifiable statements - called *Predicates* - about them.
These things - called *Particulars* - can be any entities we choose to consider.

Crucially, we represent *Particulars* through formal syntactic entities - called *Terms* -,
constructed by precise formation rules we call *Types*. Each *Type* defines what counts as
a well-formed *Particular* representation (valid *Term*).

The *Universe* of our discourse is completely determined by the *Type* that
constructs representations, i.e. *Terms*, of the *Particulars* we want to consider.
-/

namespace Universe
-- X is the type that constructs representations (*Terms*) of *Particulars* in our *Universe*
variable (X : Type)

def Particular := X
def Predicate := X → Prop

end Universe

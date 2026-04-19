The principle (now enforced)
For any CongruentUnaryPredicate U₂ produced by currying a binary relation R : U₁.Particular → U₂.Particular → Prop on its first argument, the body must put the parameter on the left and the test variable on the right:

def P_of (a: U₁.Particular): CongruentUnaryPredicate U₂ :=
  { pred := (x ↦ R a x), ... }
This way, lifting into a CongruentBinaryPredicate U₁ U₂ via G.pred x := P_of x automatically yields (G.pred x).pred y = R x y — first argument = domain, second = image, matching the binary-predicate convention. Violating the unary convention silently flips every downstream binary graph.
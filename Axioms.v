Axiom functional_extensionality : forall (A:Type) (B:A->Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

Axiom principium_tertii_exclusi : forall (P : Prop), { P }+{ ~P }.
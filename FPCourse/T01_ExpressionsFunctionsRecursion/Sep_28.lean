-- in constructive logic, you cannot prove (p or not p). We know this is true logically,
-- but we can't prove it for any p because you need a proof of p.
-- but if you don't have a proof of p or a proof of not p for the specific prop p, then
-- you can't prove it constructively.

-- proof by negation -- proves not p. Assume p, derive a contradiction, conclude not p

-- proof by contradiction. Assume not p, derive a contradiction, prove p
-- proof by contradiction is an instance of proof by negation

-- Contradiction: To P by contradiction
-- assume not p and show contradiction
-- conclude not not p.
-- not not p -> p. True, but can't prove constructively

--example {P : Prop} : ¬¬P → P :=
--  fun nnp =>
--  _

-- for all x, y element of people, x loves

-- Everyone likes someone
-- Person : Type
-- Likes : Person → Person → Prop

-- ∀ (x : Person), ∃ (y : Person, likes x y)
-- ∃ (y : Person), ∀ (x: Person, likes y x)

-- perfect numbers
-- 6: 3 + 2 + 1 = 6.
-- 28: 2+2+7+1

-- ∃ x : T, P x
-- ((w : T), (proof : P w))

-- the shape of a proof of a for all, you have a function that says you can give it any dog,
-- and it will return a proof that that dog is friendly.
-- so you take this function and apply it to a dog that isn't friendly, and you derive a contradiction

import MatchgateWidth.ThreePieceWireRouting

/-! # Injective restrictions of an actually constructed three-stage family -/
namespace MatchgateWidth
noncomputable section
namespace ThreePieceRouting
variable {B C : Type*} {x a b y : B → ℂ}

def reindex (T : ThreePieceRouting x a b y) (f : C → B) (hf : Function.Injective f) :
    ThreePieceRouting (x ∘ f) (a ∘ f) (b ∘ f) (y ∘ f) where
  left i := T.left (f i)
  middle i := T.middle (f i)
  right i := T.right (f i)
  left_simple i := T.left_simple (f i)
  middle_simple i := T.middle_simple (f i)
  right_simple i := T.right_simple (f i)
  left_middle_join i := T.left_middle_join (f i)
  middle_right_join i := T.middle_right_join (f i)
  left_disjoint := fun _ _ hij => T.left_disjoint (fun he => hij (hf he))
  middle_disjoint := fun _ _ hij => T.middle_disjoint (fun he => hij (hf he))
  right_disjoint := fun _ _ hij => T.right_disjoint (fun he => hij (hf he))
  left_middle_off i j hij := T.left_middle_off (f i) (f j) (fun he => hij (hf he))
  left_right i j := T.left_right (f i) (f j)
  middle_right_off i j hij := T.middle_right_off (f i) (f j) (fun he => hij (hf he))

@[simp] theorem reindex_wirePath (T : ThreePieceRouting x a b y) (f : C → B)
    (hf : Function.Injective f) (i : C) : (T.reindex f hf).wirePath i = T.wirePath (f i) := rfl

end ThreePieceRouting
end
end MatchgateWidth

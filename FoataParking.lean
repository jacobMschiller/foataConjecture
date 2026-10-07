import Std

/-!+# Foata compatibility for unit interval parking functions

The algorithm and the greedy parking rule are defined below. No mathematical
lemma from the paper is postulated. Only Lean's standard library is imported.
-/

namespace FoataParking

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem snoc_induction {α : Type} {P : List α → Prop}
    (hn : P []) (hs : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  have aux : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => exact hn
    | cons y ys ih => simpa using hs ys.reverse y ih
  simpa using aux xs.reverse

/-- Rotate each segment ending at a letter satisfying `p`. `acc` contains
the unfinished segment. A trailing unfinished segment is left in order. -/
def spin {α : Type} (p : α → Bool) : List α → List α → List α
  | acc, [] => acc
  | acc, x :: xs =>
      if p x then x :: (acc ++ spin p [] xs)
      else spin p (acc ++ [x]) xs

theorem spin_perm {α : Type} (p : α → Bool) (acc xs : List α) :
    (spin p acc xs).Perm (acc ++ xs) := by
  induction xs generalizing acc with
  | nil => simp [spin]
  | cons x xs ih =>
    by_cases hx : p x = true
    · simp only [spin, hx, ↓reduceIte]
      exact (List.Perm.cons x ((List.Perm.refl acc).append
        (by simpa using ih []))).trans List.perm_middle.symm
    · simp only [spin, hx, Bool.false_eq_true, ↓reduceIte]
      simpa [List.append_assoc] using ih (acc ++ [x])

theorem spin_filters {α : Type} (p : α → Bool) (acc xs : List α)
    (ha : acc.filter p = []) :
    (spin p acc xs).filter p = xs.filter p ∧
    (spin p acc xs).filter (fun x => !(p x)) =
      acc.filter (fun x => !(p x)) ++ xs.filter (fun x => !(p x)) := by
  induction xs generalizing acc with
  | nil => simp [spin, ha]
  | cons x xs ih =>
    by_cases hx : p x = true
    · have h := ih [] (by simp)
      simp [spin, hx, ha, List.filter_append, h.1, h.2]
    · have hxf : p x = false := Bool.eq_false_iff.mpr hx
      have h := ih (acc ++ [x]) (by simp [List.filter_append, ha, hxf])
      simpa [spin, hxf, List.filter_append, List.append_assoc] using h

theorem spin_map {α β : Type} (f : α → β) (p : β → Bool) (acc xs : List α) :
    (spin (fun a => p (f a)) acc xs).map f =
      spin p (acc.map f) (xs.map f) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p (f x) = true <;>
      simp [spin, hx, List.map_append, ih]

theorem spin_congr {α : Type} (p q : α → Bool) (acc xs : List α)
    (h : ∀ x ∈ xs, p x = q x) : spin p acc xs = spin q acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, p y = q y := fun y hy => h y (by simp [hy])
    simp only [spin, hx]
    split <;> simp [ih _ ht]

/-- The comparison class of the last output letter selects the cut class. -/
def cut {α : Type} (key : α → Nat) (u : List α) (x y : α) : Bool :=
  decide (key y ≤ key x) ==
    (u.map (fun z => decide (key z ≤ key x))).getLastD true

def step {α : Type} (key : α → Nat) (u : List α) (x : α) : List α :=
  spin (cut key u x) [] u ++ [x]

/-- Foata's second fundamental transformation, inserting letters left to right. -/
def foata {α : Type} (key : α → Nat) (w : List α) : List α :=
  w.foldl (step key) []

def F (w : List Nat) : List Nat := foata id w

@[simp] theorem foata_nil {α : Type} (key : α → Nat) : foata key [] = [] := rfl

theorem foata_snoc {α : Type} (key : α → Nat) (u : List α) (x : α) :
    foata key (u ++ [x]) = step key (foata key u) x := by
  simp [foata, List.foldl_append]

theorem step_perm {α : Type} (key : α → Nat) (u : List α) (x : α) :
    (step key u x).Perm (u ++ [x]) := by
  have hp : (spin (cut key u x) [] u).Perm u := by
    simpa using spin_perm (cut key u x) [] u
  exact hp.append (List.Perm.refl [x])

theorem foata_perm {α : Type} (key : α → Nat) (w : List α) :
    (foata key w).Perm w := by
  induction w using snoc_induction with
  | hn => simp
  | hs u x ih =>
    rw [foata_snoc]
    exact (step_perm key (foata key u) x).trans (ih.append (List.Perm.refl [x]))

theorem step_map {α β : Type} (f : α → β) (key : β → Nat) (u : List α) (x : α) :
    (step (fun a => key (f a)) u x).map f = step key (u.map f) (f x) := by
  have hc : cut (fun a => key (f a)) u x = fun a => cut key (u.map f) (f x) (f a) := by
    funext a
    simp [cut, List.map_map, Function.comp_def]
  simp only [step, List.map_append, List.map_cons, List.map_nil, hc]
  rw [spin_map]
  rfl

theorem foata_map {α β : Type} (f : α → β) (key : β → Nat) (w : List α) :
    (foata (fun a => key (f a)) w).map f = foata key (w.map f) := by
  induction w using snoc_induction with
  | hn => rfl
  | hs u x ih =>
    simp only [foata_snoc, List.map_append, List.map_cons, List.map_nil]
    rw [step_map, ih]

theorem step_key_congr {α : Type} (f g : α → Nat) (u : List α) (x : α)
    (h : ∀ y ∈ u, f y ≤ f x ↔ g y ≤ g x) : step f u x = step g u x := by
  have hm : u.map (fun z => decide (f z ≤ f x)) =
      u.map (fun z => decide (g z ≤ g x)) := by
    apply List.map_congr_left
    intro y hy
    simp only [h y hy]
  unfold step
  congr 1
  apply spin_congr
  intro y hy
  simp only [cut, hm, h y hy]

theorem foata_key_congr {α : Type} (f g : α → Nat) (w : List α)
    (h : w.Pairwise (fun a b => f a ≤ f b ↔ g a ≤ g b)) :
    foata f w = foata g w := by
  induction w using snoc_induction with
  | hn => rfl
  | hs u x ih =>
    have hh := List.pairwise_append.mp h
    rw [foata_snoc, foata_snoc, ih hh.1]
    apply step_key_congr
    intro y hy
    exact hh.2.2 y ((foata_perm g u).mem_iff.mp hy) x (by simp)

theorem pairwise_of_filters {α : Type} (R : α → α → Prop) (p : α → Bool)
    (u : List α) (hp : (u.filter p).Pairwise R)
    (hn : (u.filter (fun a => !(p a))).Pairwise R)
    (hc : ∀ a ∈ u, ∀ b ∈ u, p a ≠ p b → R a b) : u.Pairwise R := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have hct : ∀ x ∈ u, ∀ y ∈ u, p x ≠ p y → R x y := by
      intro x hx y hy
      exact hc x (by simp [hx]) y (by simp [hy])
    by_cases ha : p a = true
    · have hpp : (a :: u.filter p).Pairwise R := by simpa [ha] using hp
      have hnn : (u.filter (fun a => !(p a))).Pairwise R := by simpa [ha] using hn
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        by_cases hpb : p b = true
        · exact (List.pairwise_cons.mp hpp).1 b (by simp [hb, hpb])
        · exact hc a (by simp) b (by simp [hb]) (by simpa [ha] using Ne.symm hpb)
      · exact ih (List.pairwise_cons.mp hpp).2 hnn hct
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      have hpp : (u.filter p).Pairwise R := by simpa [haf] using hp
      have hnn : (a :: u.filter (fun a => !(p a))).Pairwise R := by simpa [haf] using hn
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        by_cases hpb : p b = true
        · exact hc a (by simp) b (by simp [hb]) (by simp [haf, hpb])
        · have hbf : p b = false := Bool.eq_false_iff.mpr hpb
          exact (List.pairwise_cons.mp hnn).1 b (by simp [hb, hbf])
      · exact ih hpp (List.pairwise_cons.mp hnn).2 hct

theorem spin_pairwise {α : Type} (R : α → α → Prop) (p : α → Bool)
    (u : List α) (hu : u.Pairwise R)
    (hc : ∀ a ∈ u, ∀ b ∈ u, p a ≠ p b → R a b) :
    (spin p [] u).Pairwise R := by
  have hf := spin_filters p [] u (by simp)
  have hm : ∀ a, a ∈ spin p [] u ↔ a ∈ u := by
    intro a
    simpa using (spin_perm p [] u).mem_iff (a := a)
  apply pairwise_of_filters R p
  · rw [hf.1]
    exact hu.filter p
  · rw [hf.2]
    simpa using hu.filter (fun a => !(p a))
  · intro a ha b hb
    exact hc a ((hm a).mp ha) b ((hm b).mp hb)

/-- Any ordering constraint whose only forbidden pairs have consecutive keys
is preserved by Foata on words with distinct keys. -/
theorem foata_pairwise {α : Type} (key : α → Nat) (R : α → α → Prop)
    (w : List α) (hd : w.Pairwise (fun a b => key a ≠ key b))
    (hr : w.Pairwise R)
    (hw : ∀ a ∈ w, ∀ b ∈ w, key a ≠ key b + 1 → R a b) :
    (foata key w).Pairwise R := by
  induction w using snoc_induction with
  | hn => simp
  | hs u x ih =>
    have hdd := List.pairwise_append.mp hd
    have hrr := List.pairwise_append.mp hr
    have hwt : ∀ a ∈ u, ∀ b ∈ u, key a ≠ key b + 1 → R a b := by
      intro a ha b hb
      exact hw a (by simp [ha]) b (by simp [hb])
    have hi := ih hdd.1 hrr.1 hwt
    have hm : ∀ a, a ∈ foata key u ↔ a ∈ u := fun a => (foata_perm key u).mem_iff
    rw [foata_snoc]
    unfold step
    apply List.pairwise_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · apply spin_pairwise R _ _ hi
      intro a ha b hb hc
      apply hwt a ((hm a).mp ha) b ((hm b).mp hb)
      intro hab
      have hbx : key b ≠ key x := hdd.2.2 b ((hm b).mp hb) x (by simp)
      have hcmp : (key a ≤ key x) ↔ (key b ≤ key x) := by omega
      apply hc
      simp only [cut, hcmp]
    · intro a ha b hb
      have hb' : b = x := by simpa using hb
      subst b
      have ham : a ∈ foata key u := by
        simpa using (spin_perm (cut key (foata key u) x) [] (foata key u)).mem_iff.mp ha
      exact hrr.2.2 a ((hm a).mp ham) x (by simp)

/-- A car is a pair (preference, assigned spot). -/
abbrev Car := Nat × Nat

/-- Exact greedy parking semantics: a chosen spot is free, is no smaller than
the preference, and every intervening spot is occupied by an earlier car. -/
def Parks : List Nat → List Car → Prop
  | _, [] => True
  | occupied, c :: cs =>
      c.2 ∉ occupied ∧ c.1 ≤ c.2 ∧
      (∀ t, c.1 ≤ t → t < c.2 → t ∈ occupied) ∧
      Parks (c.2 :: occupied) cs

def UnitTrace (cs : List Car) : Prop :=
  ∀ c ∈ cs, c.1 ≤ c.2 ∧ c.2 ≤ c.1 + 1

/-- A displaced car cannot precede the car in the immediately preceding spot. -/
def Dependency (a b : Car) : Prop := a.2 = b.2 + 1 → a.1 = a.2

theorem parks_fresh {occupied : List Nat} {cs : List Car} (h : Parks occupied cs)
    {c : Car} (hc : c ∈ cs) : c.2 ∉ occupied := by
  induction cs generalizing occupied with
  | nil => simp at hc
  | cons a cs ih =>
    rcases List.mem_cons.mp hc with hca | hc
    · subst c
      exact h.1
    · have ht := ih h.2.2.2 hc
      exact fun hm => ht (by simp [hm])

theorem parks_nodup {occupied : List Nat} {cs : List Car} (h : Parks occupied cs) :
    (cs.map Prod.snd).Nodup := by
  induction cs generalizing occupied with
  | nil => simp
  | cons a cs ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
      have hf := parks_fresh h.2.2.2 hc
      apply hf
      simp [he]
    · exact ih h.2.2.2

theorem parks_cover {occupied : List Nat} {cs : List Car} (h : Parks occupied cs)
    {c : Car} (hc : c ∈ cs) {t : Nat} (hl : c.1 ≤ t) (hu : t < c.2) :
    t ∈ occupied ∨ t ∈ cs.map Prod.snd := by
  induction cs generalizing occupied with
  | nil => simp at hc
  | cons a cs ih =>
    rcases List.mem_cons.mp hc with he | hc
    · subst c
      exact Or.inl (h.2.2.1 t hl hu)
    · rcases ih h.2.2.2 hc with hm | hm
      · rcases List.mem_cons.mp hm with he | hm
        · exact Or.inr (by simp [he])
        · exact Or.inl hm
      · exact Or.inr (by simp [hm])

theorem parks_compatible {occupied : List Nat} {cs : List Car}
    (hp : Parks occupied cs) (hu : UnitTrace cs) :
    cs.Pairwise (fun a b => a.1 ≤ b.1 ↔ a.2 ≤ b.2) := by
  induction cs generalizing occupied with
  | nil => simp
  | cons a cs ih =>
    have hua := hu a (by simp)
    have hut : UnitTrace cs := fun c hc => hu c (by simp [hc])
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb
      have hub := hut b hb
      have hfree := parks_fresh hp.2.2.2 hb
      have hne : b.2 ≠ a.2 := fun he => hfree (by simp [he])
      constructor
      · intro hab
        by_cases hnot : a.2 ≤ b.2
        · exact hnot
        exfalso
        have hblocked := hp.2.2.1 b.2 (by omega) (by omega)
        exact hfree (by simp [hblocked])
      · intro hab
        omega
    · exact ih hp.2.2.2 hut

theorem parks_dependencies {occupied : List Nat} {cs : List Car}
    (hp : Parks occupied cs) : cs.Pairwise Dependency := by
  induction cs generalizing occupied with
  | nil => simp
  | cons a cs ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb hab
      have hfree := parks_fresh hp.2.2.2 hb
      have hlow := hp.2.1
      by_cases hn : a.1 = a.2
      · exact hn
      exfalso
      have hblocked := hp.2.2.1 b.2 (by omega) (by omega)
      exact hfree (by simp [hblocked])
    · exact ih hp.2.2.2

/-- Unit bounds, distinct spots and the predecessor order suffice to reconstruct
the greedy trace. This is the reconstruction step of the paper's proof. -/
theorem parks_of_conditions (occupied : List Nat) (cs : List Car)
    (hf : ∀ c ∈ cs, c.2 ∉ occupied)
    (hn : (cs.map Prod.snd).Nodup)
    (hu : UnitTrace cs) (hd : cs.Pairwise Dependency)
    (hc : ∀ c ∈ cs, c.1 < c.2 → c.1 ∈ occupied ∨ c.1 ∈ cs.map Prod.snd) :
    Parks occupied cs := by
  induction cs generalizing occupied with
  | nil => trivial
  | cons a cs ih =>
    have hna := (List.nodup_cons.mp hn).1
    have hnt := (List.nodup_cons.mp hn).2
    have hua := hu a (by simp)
    have hut : UnitTrace cs := fun c hm => hu c (by simp [hm])
    have hda := (List.pairwise_cons.mp hd).1
    have hdt := (List.pairwise_cons.mp hd).2
    have hneed : a.1 < a.2 → a.1 ∈ occupied := by
      intro hlt
      rcases hc a (by simp) hlt with hm | hm
      · exact hm
      · obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
        rcases List.mem_cons.mp hb with heq | hb
        · subst b
          omega
        · have hdep := hda b hb
          have hpred : a.2 = b.2 + 1 := by omega
          have heq := hdep hpred
          omega
    refine ⟨hf a (by simp), hua.1, ?_, ?_⟩
    · intro t hlo hhi
      have he : t = a.1 := by omega
      subst t
      exact hneed hhi
    · refine ih (a.2 :: occupied) ?_ hnt hut hdt ?_
      · intro c hm
        have hcne : c.2 ≠ a.2 := by
          intro he
          apply hna
          exact List.mem_map.mpr ⟨c, hm, he⟩
        simpa using And.intro hcne (hf c (by simp [hm]))
      · intro c hm hlt
        rcases hc c (by simp [hm]) hlt with hocc | hmap
        · exact Or.inl (by simp [hocc])
        · rcases List.mem_cons.mp hmap with he | hmap
          · exact Or.inl (by simp [he])
          · exact Or.inr hmap

theorem unitTrace_perm {cs ds : List Car} (h : ds.Perm cs) (hu : UnitTrace cs) :
    UnitTrace ds := fun c hc => hu c (h.mem_iff.mp hc)

/-- Transforming cars by their spot labels preserves their entire greedy
parking trace, including each car's assigned spot. -/
theorem foata_parks {cs : List Car} (hp : Parks [] cs) (hu : UnitTrace cs) :
    Parks [] (foata Prod.snd cs) ∧ UnitTrace (foata Prod.snd cs) := by
  have hperm := foata_perm Prod.snd cs
  have hunit := unitTrace_perm hperm hu
  have hn := parks_nodup hp
  have hdistinct : cs.Pairwise (fun a b => a.2 ≠ b.2) := by
    exact List.pairwise_map.mp hn
  have hdep : (foata Prod.snd cs).Pairwise Dependency := by
    apply foata_pairwise Prod.snd Dependency cs hdistinct (parks_dependencies hp)
    intro a ha b hb hne hab
    exact False.elim (hne hab)
  refine ⟨?_, hunit⟩
  refine parks_of_conditions [] _ (by simp) ?_ hunit hdep ?_
  · exact (hperm.map Prod.snd).nodup_iff.mpr hn
  · intro c hc hlt
    have hcold := hperm.mem_iff.mp hc
    have hcov := parks_cover hp hcold (Nat.le_refl c.1) hlt
    have hold : c.1 ∈ cs.map Prod.snd := by simpa using hcov
    exact Or.inr ((hperm.map Prod.snd).mem_iff.mpr hold)

/-- The declarative greedy rule has a unique trace for any preference word. -/
theorem parks_unique {occupied : List Nat} {cs ds : List Car}
    (hc : Parks occupied cs) (hd : Parks occupied ds)
    (he : cs.map Prod.fst = ds.map Prod.fst) : cs = ds := by
  induction cs generalizing occupied ds with
  | nil =>
    have hh : ds = [] := List.eq_nil_of_map_eq_nil he.symm
    exact hh.symm
  | cons a cs ih =>
    cases ds with
    | nil => simp at he
    | cons b ds =>
      have he' := List.cons.inj he
      have hspot : a.2 = b.2 := by
        have hca := hc.2.1
        have hdb := hd.2.1
        have hpref := he'.1
        by_cases hlt : a.2 < b.2
        · have hm := hd.2.2.1 a.2 (by omega) hlt
          exact False.elim (hc.1 hm)
        by_cases hgt : b.2 < a.2
        · have hm := hc.2.2.1 b.2 (by omega) hgt
          exact False.elim (hd.1 hm)
        omega
      have hab : a = b := Prod.ext he'.1 hspot
      subst b
      have ht := ih hc.2.2.2 hd.2.2.2 he'.2
      simp [ht]

/-- The list `s` gives the actual greedy spots for preference word `w`. -/
def Realizes (w s : List Nat) : Prop :=
  ∃ cs : List Car, cs.map Prod.fst = w ∧ cs.map Prod.snd = s ∧ Parks [] cs

theorem realizes_unique {w s t : List Nat} (hs : Realizes w s) (ht : Realizes w t) :
    s = t := by
  obtain ⟨cs, hcw, hcs, hcp⟩ := hs
  obtain ⟨ds, hdw, hds, hdp⟩ := ht
  have he := parks_unique hcp hdp (hcw.trans hdw.symm)
  subst ds
  exact hcs.symm.trans hds

/-- The unique greedy outcome, chosen from its exact specification. `[]` is a
total-function fallback when no trace exists; the main theorem always supplies
a valid trace and so never uses that fallback. -/
noncomputable def spot (w : List Nat) : List Nat := by
  classical
  exact if h : ∃ s, Realizes w s then Classical.choose h else []

theorem spot_eq_of_realizes {w s : List Nat} (h : Realizes w s) : spot w = s := by
  classical
  have hex : ∃ t, Realizes w t := ⟨s, h⟩
  unfold spot
  rw [dif_pos hex]
  exact realizes_unique (Classical.choose_spec hex) h

/-- Precisely the ordinary unit interval parking condition for `w.length`
spaces numbered from 1: every preference is positive, every assigned spot is
in the lot, and each displacement is 0 or 1. -/
def IsUnitInterval (w : List Nat) : Prop :=
  ∃ cs : List Car, cs.map Prod.fst = w ∧ Parks [] cs ∧ UnitTrace cs ∧
    ∀ c ∈ cs, 0 < c.1 ∧ c.2 ≤ w.length

theorem foata_trace {cs : List Car} (hp : Parks [] cs) (hu : UnitTrace cs) :
    ∃ ds : List Car,
      ds.map Prod.fst = F (cs.map Prod.fst) ∧
      ds.map Prod.snd = F (cs.map Prod.snd) ∧
      Parks [] ds ∧ UnitTrace ds ∧ ds.Perm cs := by
  have hkey := foata_key_congr Prod.fst Prod.snd cs (parks_compatible hp hu)
  have hpark := foata_parks hp hu
  refine ⟨foata Prod.snd cs, ?_, ?_, hpark.1, hpark.2, foata_perm Prod.snd cs⟩
  · rw [← hkey]
    exact foata_map Prod.fst id cs
  · exact foata_map Prod.snd id cs

/-- Foata preserves the unit interval class, with the same finite lot size. -/
theorem foata_unitInterval {w : List Nat} (h : IsUnitInterval w) :
    IsUnitInterval (F w) := by
  obtain ⟨cs, hcw, hp, hu, hb⟩ := h
  obtain ⟨ds, hdw, hds, hdp, hdu, hperm⟩ := foata_trace hp hu
  refine ⟨ds, by simpa [hcw] using hdw, hdp, hdu, ?_⟩
  intro c hc
  have hold := hb c (hperm.mem_iff.mp hc)
  have hlen : (F w).length = w.length := (foata_perm id w).length_eq
  exact ⟨hold.1, by simpa [hlen] using hold.2⟩

/-- Conjecture 6.3: the actual greedy parking outcome commutes with Foata's
second fundamental transformation on every unit interval parking function. -/
theorem foata_spot {w : List Nat} (h : IsUnitInterval w) :
    spot (F w) = F (spot w) := by
  obtain ⟨cs, hcw, hp, hu, hb⟩ := h
  obtain ⟨ds, hdw, hds, hdp, hdu, hperm⟩ := foata_trace hp hu
  have hs : spot w = cs.map Prod.snd :=
    spot_eq_of_realizes ⟨cs, hcw, rfl, hp⟩
  have hfs : spot (F w) = ds.map Prod.snd :=
    spot_eq_of_realizes ⟨ds, by simpa [hcw] using hdw, rfl, hdp⟩
  rw [hfs, hds, hs]

/- Kernel-evaluated convention checks; no native_decide is used. -/
example : F [3, 1, 5, 3, 1, 2] = [1, 5, 3, 3, 1, 2] := by decide
example : F [3, 1, 1, 4] = [1, 3, 1, 4] := by decide
example : F [3, 1, 2, 4] = [1, 3, 2, 4] := by decide

theorem example_unit : IsUnitInterval [3, 1, 1, 4] := by
  refine ⟨[(3, 3), (1, 1), (1, 2), (4, 4)], rfl, ?_, ?_, ?_⟩
  · simp [Parks]
    refine ⟨?_, ?_, ?_⟩ <;> intro t h₁ h₂ <;> omega
  · simp [UnitTrace]
  · simp

example : spot (F [3, 1, 1, 4]) = F (spot [3, 1, 1, 4]) :=
  foata_spot example_unit

#print axioms foata_spot
#print axioms foata_unitInterval
#print axioms foata_trace

end FoataParking

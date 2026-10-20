module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
import VerifiedGarbage.Proof.MlKem.X86_64.EcBase
public import VerifiedGarbage.Proof.MlKem.X86_64.EkBase
public import VerifiedGarbage.Proof.MlKem.X86_64.DcBase
public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16

/-!
# ML-KEM on x86-64: the top-level functions with less working space

A parameter set's layout with only the first `n` bytes of `scratch`
(`narrowL`) passes the checks of the top-level functions with 16-bit
polynomials if they write no further. Their proofs against it give proofs
against the layout's own contracts (`keyGenK_widen`, …), whose `scratch` is
longer: the code runs as it does with the shorter one. Such a run leaves
the rest of `scratch` as it was (`verified_keepTail`), which is the
`Artifact.written` of the functions.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- The parameter set `L` with the first `n` bytes of `scratch`. Its code is
`L`'s: no code depends on the length of `scratch`. -/
abbrev narrowL (L : Kem) (n : Nat) : Kem := { L with scr := n }

/-- The layout `K` with the first `n` bytes of `scratch`. -/
abbrev narrowK (K : Kem16) (n : Nat) : Kem16 := { K with L := narrowL K.L n }

/-- The K-PKE functions do not depend on the length of `scratch`. -/
theorem KpkeOk.narrow {L : Kem} (h : KpkeOk L) (n : Nat) : KpkeOk (narrowL L n) where
  kg := by
    rw [show kpkeKgK (narrowL L n) = kpkeKgK L from rfl,
      show kpkeKg (narrowL L n) .avx2 keygenMul16Y = kpkeKg L .avx2 keygenMul16Y from rfl]
    exact h.kg
  enc := by
    rw [show kpkeEncK (narrowL L n) = kpkeEncK L from rfl,
      show kpkeEnc (narrowL L n) .avx2 encryptMul16Y = kpkeEnc L .avx2 encryptMul16Y from rfl]
    exact h.enc
  dec := by
    rw [show kpkeDecK (narrowL L n) = kpkeDecK L from rfl,
      show kpkeDec (narrowL L n) .avx2 Kpke16.dmInnerY = kpkeDec L .avx2 Kpke16.dmInnerY from rfl]
    exact h.dec

/-! ## Narrowing a precondition -/

/-! Each conjunct of a precondition with `scratch` of `n` bytes is that of
the one with `scratch` of `m ≥ n` bytes, or follows from a disjointness or a
bound of the longer `scratch`. -/

theorem keyGenK_pre {L : Kem} {n : Nat} (hn : n ≤ L.scr) {s : State} (hs : (keyGenK L).pre s) :
    (keyGenK (narrowL L n)).pre
      (s.withRegions s.rd [⟨s.gpr .rsi, L.ekLen⟩, ⟨s.gpr .rdx, L.dkLen⟩, ⟨s.gpr .rcx, n⟩]) := by
  obtain ⟨hrd, -, hs⟩ := hs
  refine ⟨hrd, rfl, ?_⟩
  simp only [State.withRegions_gpr]
  repeat
    obtain ⟨h, hs⟩ := hs
    refine ⟨?_, ?_⟩
    · first
        | exact h
        | exact h.sub_right (Region.sub_prefix hn)
        | exact h.sub_left (Region.sub_prefix hn)
        | exact Nat.le_trans (Nat.add_le_add_left hn _) h
  first | exact hs | exact Nat.le_trans (Nat.add_le_add_left hn _) hs

theorem encapsK_pre {L : Kem} {n : Nat} (hn : n ≤ L.scr) {s : State} (hs : (encapsK L).pre s) :
    (encapsK (narrowL L n)).pre
      (s.withRegions s.rd [⟨s.gpr .rcx, 32⟩, ⟨s.gpr .r8, L.ctLen⟩, ⟨s.gpr .r9, n⟩]) := by
  obtain ⟨hrd, -, hs⟩ := hs
  refine ⟨hrd, rfl, ?_⟩
  simp only [State.withRegions_gpr]
  repeat
    obtain ⟨h, hs⟩ := hs
    refine ⟨?_, ?_⟩
    · first
        | exact h
        | exact h.sub_right (Region.sub_prefix hn)
        | exact h.sub_left (Region.sub_prefix hn)
        | exact Nat.le_trans (Nat.add_le_add_left hn _) h
  first | exact hs | exact Nat.le_trans (Nat.add_le_add_left hn _) hs

theorem encK_pre {L : Kem} {n : Nat} (hn : n ≤ L.scr) {s : State} (hs : (encK L).pre s) :
    (encK (narrowL L n)).pre
      (s.withRegions s.rd [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.ctLen⟩, ⟨s.gpr .r8, n⟩]) := by
  obtain ⟨hrd, -, hs⟩ := hs
  refine ⟨hrd, rfl, ?_⟩
  simp only [State.withRegions_gpr]
  repeat
    obtain ⟨h, hs⟩ := hs
    refine ⟨?_, ?_⟩
    · first
        | exact h
        | exact h.sub_right (Region.sub_prefix hn)
        | exact h.sub_left (Region.sub_prefix hn)
        | exact Nat.le_trans (Nat.add_le_add_left hn _) h
  first | exact hs | exact Nat.le_trans (Nat.add_le_add_left hn _) hs

theorem decapsK_pre {L : Kem} {n : Nat} (hn : n ≤ L.scr) {s : State} (hs : (decapsK L).pre s) :
    (decapsK (narrowL L n)).pre (s.withRegions s.rd [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, n⟩]) := by
  obtain ⟨hrd, -, hs⟩ := hs
  refine ⟨hrd, rfl, ?_⟩
  simp only [State.withRegions_gpr]
  repeat
    obtain ⟨h, hs⟩ := hs
    refine ⟨?_, ?_⟩
    · first
        | exact h
        | exact h.sub_right (Region.sub_prefix hn)
        | exact h.sub_left (Region.sub_prefix hn)
        | exact Nat.le_trans (Nat.add_le_add_left hn _) h
  first | exact hs | exact Nat.le_trans (Nat.add_le_add_left hn _) hs

/-! ## Widening the contracts -/

/-- The writable regions with the first `n` bytes of `scratch`, extended by
those with all of it. -/
theorem prefix3 {a b c : Addr} {x y n m : Nat} (hn : n ≤ m) :
    List.Forall₂ Region.Prefix [⟨a, x⟩, ⟨b, y⟩, ⟨c, n⟩] [⟨a, x⟩, ⟨b, y⟩, ⟨c, m⟩] :=
  .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hn⟩ .nil))

theorem prefix2 {a c : Addr} {x n m : Nat} (hn : n ≤ m) :
    List.Forall₂ Region.Prefix [⟨a, x⟩, ⟨c, n⟩] [⟨a, x⟩, ⟨c, m⟩] :=
  .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hn⟩ .nil)

theorem keyGenK_widen {L : Kem} {n : Nat} (hn : n ≤ L.scr) {c : Prog isa}
    (h : Verified target c (keyGenK (narrowL L n))) (hsat : ∃ s, (keyGenK L).pre s) :
    Verified target c (keyGenK L) :=
  X86_64.Verified.widen h (fun s => [⟨s.gpr .rsi, L.ekLen⟩, ⟨s.gpr .rdx, L.dkLen⟩, ⟨s.gpr .rcx, n⟩])
    (fun _ hs => keyGenK_pre hn hs) (fun _ hs => by rw [hs.2.1]; exact prefix3 hn)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem encapsK_widen {L : Kem} {n : Nat} (hn : n ≤ L.scr) {c : Prog isa}
    (h : Verified target c (encapsK (narrowL L n))) (hsat : ∃ s, (encapsK L).pre s) :
    Verified target c (encapsK L) :=
  X86_64.Verified.widen h (fun s => [⟨s.gpr .rcx, 32⟩, ⟨s.gpr .r8, L.ctLen⟩, ⟨s.gpr .r9, n⟩])
    (fun _ hs => encapsK_pre hn hs) (fun _ hs => by rw [hs.2.1]; exact prefix3 hn)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem encK_widen {L : Kem} {n : Nat} (hn : n ≤ L.scr) {c : Prog isa}
    (h : Verified target c (encK (narrowL L n))) (hsat : ∃ s, (encK L).pre s) :
    Verified target c (encK L) :=
  X86_64.Verified.widen h (fun s => [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.ctLen⟩, ⟨s.gpr .r8, n⟩])
    (fun _ hs => encK_pre hn hs) (fun _ hs => by rw [hs.2.1]; exact prefix3 hn)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem decapsK_widen {L : Kem} {n : Nat} (hn : n ≤ L.scr) {c : Prog isa}
    (h : Verified target c (decapsK (narrowL L n))) (hsat : ∃ s, (decapsK L).pre s) :
    Verified target c (decapsK L) :=
  X86_64.Verified.widen h (fun s => [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, n⟩])
    (fun _ hs => decapsK_pre hn hs) (fun _ hs => by rw [hs.2.1]; exact prefix2 hn)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-! ## What the rest of `scratch` holds -/

/-- Code verified against `k`, run from a state that permits writing regions
extending `wr`, with which it meets `k`'s precondition, changes no byte
outside `wr` and the 32 bytes of stack below `rsp`, if it writes `rsp` only
in its frames and its calls and frames use at most those 32 bytes. -/
theorem verified_keep {c : Prog isa} {k : Contract isa} (hv : Verified target c k) (hsp : SpSafe c)
    (hd : c.x86_64Depth ≤ 32) {s : State} {wr : List Region} (hpre : k.pre (s.withRegions s.rd wr))
    (hwr : List.Forall₂ Region.Prefix wr s.wr) {t : List Leak} {s' : State} (he : Exec isa c s t s')
    {x : Addr} (hx : ∀ r ∈ wr ++ [below (s.gpr .rsp) 32], ¬ r.Contains x 1) : s'.mem x = s.mem x := by
  obtain ⟨t₁, s₁, he₁, -⟩ := hv.1 _ hpre
  have hw : Covers wr s.wr := fun _ _ => InRegions.of_prefix hwr
  have he' := Exec.widen he₁ (rd := s.rd) (wr := s.wr) (by simpa using (Covers.refl _).append hw) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  obtain ⟨-, rfl⟩ := Exec.det he he'
  have hf := Exec.stackFrame hsp he₁ (by omega)
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem] at hf
  simp only [State.withRegions_mem]
  refine hf x fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r (List.mem_append_left _ hr)
  · rw [List.mem_singleton] at hr
    subst hr
    exact fun hc => hx _ (List.mem_append_right _ (List.mem_singleton_self _))
      (Offset.sub_below _ (by omega) (by omega) x hc)

/-- The bytes of `scratch` (`len` bytes at `p`) from its `n`-th on, which a
run as in `verified_keep` leaves as they were if the regions it may write are
the first `n` bytes of `scratch` and others apart from `scratch`, and so is
the stack below `rsp`. -/
theorem verified_keepTail {c : Prog isa} {k : Contract isa} (hv : Verified target c k) (hsp : SpSafe c)
    (hd : c.x86_64Depth ≤ 32) {s : State} {wr : List Region} (hpre : k.pre (s.withRegions s.rd wr))
    (hwr : List.Forall₂ Region.Prefix wr s.wr) {t : List Leak} {s' : State} (he : Exec isa c s t s')
    {p : Addr} {n len : Nat} (hp : p.toNat + len ≤ 2 ^ 64)
    (hws : ∀ r ∈ wr, r = ⟨p, n⟩ ∨ r.Disjoint ⟨p, len⟩) (hstk : (below (s.gpr .rsp) 32).Disjoint ⟨p, len⟩)
    {i : Nat} (hi : n ≤ i) (hil : i < len) :
    s'.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
  have hil' : i < 2 ^ 64 := by have := p.isLt; omega
  have hin : (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := Offset.contains_base p (by omega) hil'
  refine verified_keep hv hsp hd hpre hwr he fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hws r hr with rfl | hdj
    · simp only [Region.Contains]
      rw [Mem.sub_ofNat_toNat p hil']
      omega
    · exact fun hc => hdj _ hc hin
  · rw [List.mem_singleton] at hr
    subst hr
    exact fun hc => hstk _ hc hin

end VG.Proof.MlKem.X86_64

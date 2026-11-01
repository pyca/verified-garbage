module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Site
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Prf
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-DSA on PPC64LE: bytes, copies and the sponge in the buffers of a `Site`

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Steps.lean`): a byte stored
(`setB_ok`), bytes copied (`copyS`, from ML-KEM's `copyL`), and the sponge
(`hashS`, from ML-KEM's `hash_ok`), with what they change as triples of the
layout.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Impl.MlKem.PPC64LE (Piece hash copy copyBody)
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad rates)

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s)
include hs

/-! ## A byte -/

theorem setB_ok {q : Ptr} (pq : PtrIn L q 1) (hw : ix q.1 ∈ Wb) (ho : q.2 < 2 ^ 15) {v : Nat} (hv : v < 2 ^ 15) :
    WP isa (.block (setB q v)) s fun s' =>
      Kept (L.RL [tri q 1]) s s' ∧ bytesAt s'.mem (lpa L q) 1 = [BitVec.ofNat 8 v] := by
  have gb := hs.base (baseReg_of pq.1)
  have hn : q.1 ≠ .r0 := by
    have := baseReg_of pq.1; simp only [baseReg, Bool.or_eq_true, beq_iff_eq] at this
    rcases this with ((h | h) | h) | h <;> rw [h] <;> decide
  have hi : InRegions s.wr (lpa L q) 1 := hs.cwE pq hw _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have sk := VG.Proof.MlKem.PPC64LE.setWidth8_ofNat (N := v) (by omega)
  have hmv : WP isa (.block (setB q v)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem.writeW (lpa L q) (BitVec.ofNat 8 v) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    simp only [lpa, Lay.A, ← gb] at hi ⊢
    prun [setB, exec_stb, hn, ho, hv, hi, sk]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | (intro r hr
         have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
         simp only [RegUpd.gpr_write, h0, ite_false])
  refine WP.mono hmv fun s' ⟨cs, m, rd, wr, sp⟩ => ⟨⟨cs, sp, rd, wr, ?_⟩, ?_⟩
  · rw [m]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [m, show ∀ (m : Mem) (a : Addr), bytesAt m a 1 = [m a] from fun _ _ => by simp [bytesAt],
      VG.WriteBytes.writeW8_apply, ite_eq_left rfl]

/-! ## A copy -/

theorem copyS {sb db : Reg} {so dO len : Nat} (ps : PtrIn L (sb, so) len) (pd : PtrIn L (db, dO) len)
    (wd : ix db ∈ Wb) (hse : so < 32768) (hde : dO < 32768) (hle : len < 32768) (hl0 : 0 < len)
    (hd : sepB L.sizes (tri (sb, so) len) (tri (db, dO) len) = true) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [tri (db, dO) len]) s s' ∧ bytesAt s'.mem (lpa L (db, dO)) len = bytesAt s.mem (lpa L (sb, so)) len := by
  have hsb := baseReg_of ps.1
  have hdb := baseReg_of pd.1
  refine WP.seq (WP.mono (copy_setup (base_pres hsb) (base_pres hdb) hse hde hle) fun s₁ ⟨o₁, g3, g4, g5⟩ => ?_)
  rw [hs.base hsb] at g3; rw [hs.base hdb] at g4
  refine WP.mono (copy_loop (by omega) hl0 (hs.dE hd (.inr wd))
    (by rw [o₁.rd, o₁.wr]; exact hs.crE ps)
    (by rw [o₁.wr]; exact hs.cwE pd wd) g3 g4 g5)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨(o₁.kept _).trans ⟨cs, sp, rd, wr, fr⟩, ?_⟩
  rw [o₁.mem] at hb; exact hb

/-! ## The sponge -/

theorem hashS {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hsfx : sfx < 256) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk (hashLay L s K) ix s false p) (hq : PieceOk (hashLay L s K) ix s true q) :
    WP isa (hash rate sfx ins [q]) s fun s' =>
      Kept (L.RL [(0, 0, 200), (0, 200, 640), (1, 0, STK), (ix q.base, q.off, q.len)]) s s' ∧
      bytesAt s'.mem (L.A (ix q.base) q.off) q.len = squeezeFrom rate (absorb rate
        (pad rate (BitVec.ofNat 8 sfx) (ins.map ((hashLay L s K).pb ix s.mem)).flatten)) 0 q.len := by
  refine WP.mono (hash_ok hrate hsfx (hs.ctx hK) hne hin (fun p hp => by
    rw [List.mem_singleton] at hp; subst hp; exact hq) (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ => ⟨?_, ?_⟩
  · refine ⟨k.cs, k.sp, k.rd, k.wr, k.frame.sub fun r hr => ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
        rw [hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      have := hs.belowSub (n := 48) hs.s48
      simp only [below] at this
      intro x hx
      apply this
      simpa [Lay.R, hashLay] using hx
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), by
        rw [hashLay_R L s K (ix_ne1 _)]; exact fun _ h => h⟩
  · have := o.1
    simp only [Lay.pb, hashLay_ptr L s K (ix_ne1 _)] at this
    exact this

/-- A piece of the sponge, in a buffer of the layout. -/
theorem pieceS {K : Nat → Bool} {w : Bool} {p : Piece} (hb : baseReg p.base = true)
    (hoe : p.off < 32768) (hle : p.len < 32768) (hpos : 0 < p.len)
    (hsep : sepAll (hashLay L s K).sizes (ix p.base, p.off, p.len) kRegs = true)
    (hK : ix p.base = 0 ∨ K (ix p.base) = true) (hw : w = true → ix p.base ∈ Wb) :
    PieceOk (hashLay L s K) ix s w p := by
  have hi5 := ix_lt hb
  have e := hashLay_size L s (ix_ne1 p.base) hK hi5
  refine ⟨base_pres hb, by rw [hashLay_ptr L s K (ix_ne1 _)]; exact hs.base hb, hoe, hle, hpos, hsep, ?_⟩
  rw [hashLay_ptr L s K (ix_ne1 _), e]
  cases w with
  | true => exact hs.cw _ (hw rfl) (ix_ne1 _)
  | false => exact hs.cr _ hi5 (ix_ne1 _)

end

/-! ## What a part keeps -/

section
variable {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
  (hf : Frame (L.RL W) m m') {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : i ∈ Wb)
include hL hf h hw

omit hf in
theorem keepD : ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := fun r hr => by
  obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
  exact disjW hL (List.all_eq_true.mp h w hw') (.inl hw)

theorem bytes_keepW (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (keepD hL h hw) hl

section
variable (hl : l = 1024)
include hl

theorem polyIs_keepW {f : Spec.MlDsa.Poly} (hp : Proof.MlDsa.PolyIs m (L.A i o) f) : Proof.MlDsa.PolyIs m' (L.A i o) f :=
  Proof.MlDsa.Verify.polyIs_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this) hp

theorem reduced_keepW (hp : Proof.MlDsa.Reduced m (L.A i o)) : Proof.MlDsa.Reduced m' (L.A i o) :=
  Proof.MlDsa.Verify.reduced_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this) hp

theorem polyAt_keepW : Proof.MlDsa.polyAt m' (L.A i o) = Proof.MlDsa.polyAt m (L.A i o) :=
  Proof.MlDsa.Verify.polyAt_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this)

theorem natPolyAt_keepW : Proof.MlDsa.natPolyAt m' (L.A i o) = Proof.MlDsa.natPolyAt m (L.A i o) :=
  Proof.MlDsa.Verify.natPolyAt_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this)

end

end

end VG.Proof.MlDsa.PPC64LE.KeyGen

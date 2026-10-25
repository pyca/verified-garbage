module

import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Timing
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLocal
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyRoot
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The fixed-address prefix initializes all public verification digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (BITS)

/-- Everything before the joint multiplication. -/
def verifyPrefix (fld : Impl.X448.X86_64.Field) (rt : Prog isa) : Prog isa :=
  .seq (.seq (.seq (.seq (.block ventry) vbits) (.block vstart)) (vdecode fld rt)) (.block (vnegA fld))

theorem verifyPrefix_ok {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)
    (hR : RecoverOk) {rt : Prog isa} (hrt : RootOk rt) {s : State} (hp : verifyEquationLocal.pre s) :
    WP isa (verifyPrefix fld rt) s (Window.JointTimingCtx (s.gpr .rcx) (signatureScalar s) (challengeScalar s)) := by
  obtain ⟨hr, hw, hdk, hds, hdc, hret, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rcx = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hret hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdi, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have rsg : ∀ i n, i + n ≤ 114 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rsi, 114⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 114) h (by omega)⟩
  have rch : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdx, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdi + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hds (by omega) (by decide)
  have fs : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) :=
    fun i hi => by rw [Offset.add_add]; exact far hds (by omega) (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = K := ⟨_, rfl⟩
  rw [verifyPrefix]
  apply WP.assoc'
  apply WP.assoc'
  apply WP.assoc'
  -- The entry: the callee-saved registers saved, and the pointers.
  apply WP.seq
  refine WP.mono (ventry_ok hbase hws hn) fun s1 ⟨hs1, sv1, r81, r91, si1, g1, o1, rd1, wr1⟩ => ?_
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [rd1, wr1]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `k` and `S`.
  apply WP.seq
  refine WP.mono (vbits_ok (sig := s.gpr .rsi) (ch := s.gpr .rdx) hs1 si1 r91
    (fun q hq => by rw [rr1, Offset.add_add]; exact rsg _ _ (by omega))
    (fun q hq => by rw [rr1]; exact rch _ _ (by omega)) fs fch)
    fun s2 ⟨bs2, bk2, si2, g2, rd2, wr2, o2⟩ => ?_
  rw [far_bytes O1 fs, hS] at bs2
  rw [far_bytes O1 fch, hK] at bk2
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hn⟩
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rd1, wr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  -- The pointers saved, and the check of `S`.
  apply WP.seq
  refine WP.mono (vstart_ok (pk := s.gpr .rdi) (sig := s.gpr .rsi) hs2 (by rw [g2 _ (by decide), r81]) (by rw [g2 _ (by decide), r91]) si2
    (fun i hi => by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega))
    (by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega)) fs)
    fun s3 ⟨pk3, sig3, ⟨c0, hc0, b3⟩, g3, rd3, wr3, o3⟩ => ?_
  rw [far_bytes O2 fs, hS] at hc0
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hn⟩
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [rd3, wr3, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (o3.mono (by decide) (by decide))
  -- `R` and `A`, decoded by one loop.
  apply WP.seq
  refine WP.mono (vdecode_ok hf hR hrt hs3 pk3 sig3 (fun i n h => by rw [rr3]; exact rpk i n h)
    (fun i n h => by rw [rr3]; exact rsg i n (by omega)) fpk fsg)
    fun s4 ⟨⟨cR, cA, hcR, hcA, b4⟩, vr4, va4, g4, rd4, wr4, D4⟩ => ?_
  rw [far_bytes O3 fpk] at hcA va4
  rw [far_bytes O3 fsg, ← bytesAt_take57] at hcR vr4
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hn⟩
  have O4 : Outside base 0 8192 s.mem s4.mem := O3.trans (D4.wide.mono (by decide) (by decide))
  -- `A` negated, and the constants.
  refine WP.mono (vnegA_ok hf hs4) fun s4' ⟨n6, n7, n10, p4, q4, d4, g4', rd4', wr4', o4⟩ => ?_
  have hs4' : Scr s4' base := ⟨(g4' _ (by decide)).trans hs4.rdi, wr4' ▸ hs4.wr, hn⟩
  have bits4 : ∀ o : Nat, o + 460 ≤ 8192 → 2048 ≤ o → ∀ t < 461,
      s4'.mem (off base (o - 1 + t)) = s2.mem (off base (o - 1 + t)) := fun o ho1 ho2 t ht => by
    have hofs := VG.Proof.X448.X86_64.ofs_off' base (d := o - 1 + t) (by omega)
    rw [o4 _ (Or.inr (by rw [hofs]; omega)), D4.wide _ (Or.inr (by rw [hofs]; omega)),
      o3 _ (Or.inr (by rw [hofs]; simp only [KC]; omega))]
  have bs4 : Window.Bits base BITS S s4' := by
    intro t ht
    rw [bits4 BITS (by decide) (by decide) t ht, bs2 t ht]
  have bk4 : Window.Bits base KBITS K s4' := by
    intro t ht
    rw [bits4 KBITS (by decide) (by decide) t ht, bk2 t ht]
  simpa only [signatureScalar, challengeScalar, hS, hK, hbase] using
    (show Window.JointTimingCtx base S K s4' from ⟨hs4', bs4, bk4, d4, n10, p4⟩)

end VG.Proof.Ed448.X86_64

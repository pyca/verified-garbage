module

public import VerifiedGarbage.Proof.MlKem.X86_64.Top768
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86_64Impl
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Sel
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Sel
import VerifiedGarbage.Proof.MlKem.X86_64.EcP16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EcP16
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
meta import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Impl.MlKem.X86_64.Wipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
import VerifiedGarbage.Proof.MlKem1024.X86_64.Written
public import VerifiedGarbage.Proof.MlKem.Scrubbed
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-KEM on x86-64: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/X86_64.lean`) of its code, which zeroes the bytes
of `scratch` that code may write once it returns, with an implementation of
`vg_zeroize` (`ZeroizeImpl`), and is verified against the same contract with
24 more bytes of stack and `scratch` left scrubbed (`*_scrubbed`, the
contracts of `Proof/MlKem/Scrubbed.lean`): ML-KEM-768's zeroes all of it
(`Verified.callWipe'`, `Scrubbed.keyGen_wiped`, …), and ML-KEM-1024's all of
it or, with 16-bit polynomials, the first `scr16` bytes, the others of which
its code leaves unchanged (`Verified.callWipeTail'`, `keyGen1024_tail`, …).
`*_verified` are those weakened to the contracts of `Spec/MlKem/`, which do
not state it yet.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64

/-! ## The stack the functions use -/

theorem xdLe_s4 (v : Sample4Impl) {k : Nat} (hk : 24 ≤ k) : xdLe k v.callee.code = true :=
  xdLe_of_le (by rw [x86_64Depth_noSp v.nosp]; have := v.depth_le; omega)

theorem Codecs.ce_xd {k : Nat} (cs : Codecs) : xdLe k cs.ce = true :=
  xdLe_of_le (by rw [x86_64Depth_zero (Codecs.ceI cs).nosp (Codecs.ceI cs).depth]; exact Nat.zero_le _)

theorem Codecs.dd_xd {k : Nat} (cs : Codecs) : xdLe k cs.dd = true :=
  xdLe_of_le (by rw [x86_64Depth_zero (Codecs.ddI cs).nosp (Codecs.ddI cs).depth]; exact Nat.zero_le _)

theorem xdLe_seqR_zero {k : Nat} (f : Nat → Prog isa) (a : Nat) : xdLe k (seqR f a 0) = true := rfl

theorem xdLe_seqR_succ {k : Nat} {f : Nat → Prog isa} {a n : Nat} (h₁ : xdLe k (f a) = true)
    (h₂ : xdLe k (seqR f (a + 1) n) = true) : xdLe k (seqR f a (n + 1)) = true :=
  xdLe_seq h₁ h₂

theorem ce768_xd {k : Nat} (cs : Codecs) : xdLe k (kem768w.L.ce cs) = true := Codecs.ce_xd cs
theorem dd768_xd {k : Nat} (cs : Codecs) : xdLe k (kem768w.L.dd cs) = true := Codecs.dd_xd cs

theorem ce1024_xd {k : Nat} : ∀ cs : Codecs, xdLe k (kem1024w.L.ce cs) = true
  | .base => xdLe_of_le (by rw [show (kem1024w.L.ce .base).x86_64Depth = 0 by decide +kernel]; exact Nat.zero_le _)
  | .avx2 => xdLe_of_le (by rw [show (kem1024w.L.ce .avx2).x86_64Depth = 0 by decide +kernel]; exact Nat.zero_le _)

theorem dd1024_xd {k : Nat} : ∀ cs : Codecs, xdLe k (kem1024w.L.dd cs) = true
  | .base => xdLe_of_le (by rw [show (kem1024w.L.dd .base).x86_64Depth = 0 by decide +kernel]; exact Nat.zero_le _)
  | .avx2 => xdLe_of_le (by rw [show (kem1024w.L.dd .avx2).x86_64Depth = 0 by decide +kernel]; exact Nat.zero_le _)

theorem xdLe_block {k : Nat} (l : List Instr) : xdLe k (.block l) = true := rfl

/-- That the calls of code that calls the implementation `v` use at most `k`
bytes of stack (a goal `xdLe k _ = true`). -/
tactic_template "s4_xd " v:ident : tactic =>
  `(tactic| repeat' (first
    | (closed_in $v; decide +kernel)
    | with_reducible exact xdLe_s4 $v (by decide)
    | with_reducible exact xdLe_prfs $v _ _ _ _ (by decide)
    | with_reducible exact xdLe_callee (($v).arith.dm _ (by decide))
    | with_reducible exact xdLe_callee (($v).arith.em _ (by decide))
    | with_reducible exact xdLe_callee (($v).arith.km _ (by decide))
    | with_reducible exact xdLe_callee ($v).arith.nttInv | with_reducible exact xdLe_callee ($v).arith.add
    | with_reducible exact xdLe_callee ($v).arith.sub | with_reducible exact xdLe_callee ($v).arith.cbd
    | with_reducible exact xdLe_callee ($v).arith.cbd16 | with_reducible exact xdLe_callee ($v).arith.dec12
    | with_reducible exact xdLe_callee ($v).arith.enc12
    | with_reducible exact Codecs.ce_xd _ | with_reducible exact Codecs.dd_xd _
    | with_reducible exact ce768_xd _ | with_reducible exact dd768_xd _
    | with_reducible exact ce1024_xd _ | with_reducible exact dd1024_xd _
    | with_reducible exact xdLe_seqR_zero _ _ | with_reducible apply xdLe_seqR_succ
    | with_reducible exact xdLe_block _
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite)
    | (code_whnf; with_reducible apply xdLe_call)))

theorem xdLe_batchHM {k m : Nat} {b : Prog isa} (B : BatchHMOk16 m b) : xdLe k b = true :=
  xdLe_of_le (by rw [B.xd]; exact Nat.zero_le _)

theorem xdLe_batchP {k N₀ m : Nat} {b : Prog isa} (B : BatchPOk16 N₀ m b) : xdLe k b = true :=
  xdLe_of_le (by rw [B.xd]; exact Nat.zero_le _)

/-- As `s4_xd`, for key generation with the fragments `b` and `p` (`B`, `P`)
and the halves of K-PKE key generation (`hR`). -/
tactic_template "kgh_xd " v:ident b:ident p:ident B:ident P:ident hR:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact xdLe_batchHM ($B _ (by decide)) | with_reducible exact xdLe_batchP ($P (_, _) (by decide))
    | with_reducible exact xdLe_callee ($hR).ntt | with_reducible exact xdLe_callee ($hR).row
    | (closedH_in $v $b $p; decide +kernel) | (code_whnf; closedH_in $v $b $p; decide +kernel)
    | with_reducible exact xdLe_prfs $v _ _ _ _ (by decide) | with_reducible exact xdLe_callee ($v).arith.cbd16
    | with_reducible exact xdLe_seqR_zero _ _ | with_reducible apply xdLe_seqR_succ
    | with_reducible exact xdLe_block _
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite)
    | (code_whnf; with_reducible apply xdLe_call)))

/-- As `s4_xd`, for encapsulation with the fragment `p` (`P`) and the K-PKE
functions (`hK`). -/
tactic_template "ecp_xd " v:ident p:ident P:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact xdLe_batchP ($P (_, _) (by decide)) | with_reducible exact xdLe_callee ($hK).enc
    | (closedP_in $v $p; decide +kernel) | (code_whnf; closedP_in $v $p; decide +kernel)
    | with_reducible exact xdLe_callee ($v).arith.cbd16
    | with_reducible exact xdLe_seqR_zero _ _ | with_reducible apply xdLe_seqR_succ
    | with_reducible exact xdLe_block _
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite)
    | (code_whnf; with_reducible apply xdLe_call)))

/-! Each choice of code, for a property `P` of each code it chooses among. -/

theorem keyGenSel_of {K : Kem16} (v : Sample4Impl) {P : Prog isa → Prop}
    (h16 : ∀ n c, S16Ok c → P (kemKeyGen16 K v.callee (n, c))) (h : P (kemKeyGen K.L v.callee)) :
    P (kemKeyGenSel K v.callee) := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

theorem encapsHSel_of {K : Kem16} (v : Sample4Impl) {P : Prog isa → Prop}
    (h16 : ∀ n c, S16Ok c → P (kemEncapsH16 K v.callee (n, c))) (h : P (kemEncapsH K.L v.callee)) :
    P (kemEncapsHSel K v.callee) := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

theorem encapsSel_of {K : Kem16} (v : Sample4Impl) {P : Prog isa → Prop}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → P (kemEncaps16 K v.callee (n, c) b))
    (h : P (kemEncaps K.L v.callee)) : P (kemEncapsSel K v.callee) := by
  unfold kemEncapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

theorem decapsSel_of {K : Kem16} (v : Sample4Impl) {P : Prog isa → Prop}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → P (kemDecapsJ16 K v.callee (n, c) b))
    (h : P (kemDecaps K.L v.callee)) : P (kemDecapsSel K v.callee) := by
  unfold kemDecapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

theorem keyGenHSel_of (v : Sample4Impl) {P : Prog isa → Prop}
    (hH : ∀ (b : Nat → Prog isa) (p : Nat → Nat → Prog isa), (∀ m ≤ 3, BatchHMOk16 m (b m)) →
      (∀ q ∈ Impl.MlKem.X86_64.Sample4.pnUses, BatchPOk16 q.1 q.2 (p q.1 q.2)) →
      P (kemKeyGenH16 kem768w v.callee b p))
    (h : P (kemKeyGenSel kem768w v.callee)) : P (kemKeyGenHSel v.callee) := by
  unfold kemKeyGenHSel
  match hb : v.callee.batchHM16, hpb : v.callee.batchP16 with
  | some b, some p => exact hH b p (v.batchHM16 b hb) (v.batchP16 p hpb)
  | none, _ => exact h
  | some _, none => exact h

theorem encapsHPSel_of (v : Sample4Impl) {P : Prog isa → Prop}
    (hP : ∀ p : Nat → Nat → Prog isa, (∀ q ∈ Impl.MlKem.X86_64.Sample4.pnUses, BatchPOk16 q.1 q.2 (p q.1 q.2)) →
      P (kemEncapsHP16 kem768w v.callee p))
    (h : P (kemEncapsHSel kem768w v.callee)) : P (kemEncapsHPSel v.callee) := by
  unfold kemEncapsHPSel
  match hs : v.callee.s16, hpb : v.callee.batchP16 with
  | some _, some p => exact hP p (v.batchP16 p hpb)
  | none, _ => exact h
  | some _, none => exact h

/-! The calls and frames of each function use at most 32 bytes of stack. -/

theorem keyGen_xd (v : Sample4Impl) : (keyGen v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (keyGenHSel_of (P := fun c => xdLe 32 c = true) v (fun b p B P => by kgh_xd v b p B P kgRows768)
    (keyGenSel_of (P := fun c => xdLe 32 c = true) v (fun _ c S => by s16_xd v c S kpke768) (by s4_xd v)))

theorem encapsH_xd (v : Sample4Impl) : (encapsH v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (encapsHPSel_of (P := fun c => xdLe 32 c = true) v (fun p P => by ecp_xd v p P kpke768)
    (encapsHSel_of (P := fun c => xdLe 32 c = true) v (fun _ c S => by s16_xd v c S kpke768) (by s4_xd v)))

theorem encaps_xd (v : Sample4Impl) : (encaps v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (encapsSel_of (P := fun c => xdLe 32 c = true) v
    (fun _ c b S B => by ek16_xd v c b S B kpke768) (by s4_xd v))

theorem decaps_xd (v : Sample4Impl) : (decaps v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (decapsSel_of (P := fun c => xdLe 32 c = true) v
    (fun _ c b S B => by ek16_xd v c b S B kpke768) (by s4_xd v))

theorem keyGen1024_xd (v : Sample4Impl) : (keyGen1024 v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (keyGenSel_of (P := fun c => xdLe 32 c = true) v
    (fun _ c S => by s16_xd v c S kpke1024) (by s4_xd v))

theorem encapsH1024_xd (v : Sample4Impl) : (encapsH1024 v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (encapsHSel_of (P := fun c => xdLe 32 c = true) v
    (fun _ c S => by s16_xd v c S kpke1024) (by s4_xd v))

theorem encaps1024_xd (v : Sample4Impl) : (encaps1024 v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (encapsSel_of (P := fun c => xdLe 32 c = true) v
    (fun _ c b S B => by ek16_xd v c b S B kpke1024) (by s4_xd v))

theorem decaps1024_xd (v : Sample4Impl) : (decaps1024 v.callee).x86_64Depth ≤ 32 :=
  xdLe_spec (decapsSel_of (P := fun c => xdLe 32 c = true) v
    (fun _ c b S B => by ek16_xd v c b S B kpke1024) (by s4_xd v))

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega) (by omega))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega)
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega) hj hij hw

/-! ## Wiping only what the code writes

With 16-bit polynomials, ML-KEM-1024's code writes only the first `scr16`
bytes of `scratch` (`Proof/MlKem1024/X86_64/Written.lean`), and `callWipe`
zeroes only those (`wiped1024`, `wipedEnc1024`). Its postcondition with the
other bytes unchanged (`tail4`, `tail5`, `tail6`: `scratch` is the last
argument) is then the one `Verified.callWipeTail'` takes, which reads the
memory on return only apart from the bytes zeroed (`tail4_out`, …), and
with those zero, `scratch` is scrubbed (`wipedTail4`, …). -/

open VG.Proof.MlKem.Scrubbed (Post4 Post5 Post6 scrub4 scrub5 scrub6 scrubbed_of_prefix)

/-- A proof against `sig.contract abi pre P …` of code that changes no byte
of the arrays `ws` names past their bounds is one against
`sig.contract abi pre P' …`, for `P'` that `P` and those bytes unchanged
imply. -/
theorem Verified.tail_of_written {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {P P' : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}
    {ws : List (String × Nat)}
    (h : Verified X86_64.target c (sig.contract abi pre P wa stack leak))
    (hk : (sig.words abi.ptrBits).length ≤ 6)
    (hw : ∀ s t s', (sig.contract abi pre P wa stack leak).pre s → Exec isa c s t s' →
      Sig.writtenWithin (abi.withConsts []) sig ws s s')
    (hP : ∀ vs m m' x, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) P vs m m' x →
      (∀ y ∈ ws, ∀ b ∈ Sig.arrays sig.params vs, b.1 = y.1 → ∀ i, y.2 ≤ i → i < b.2.len →
        m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply (sig.words abi.ptrBits) P' vs m m' x) :
    Verified X86_64.target c (sig.contract abi pre P' wa stack leak) := by
  obtain ⟨hc, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, hct, hsat⟩
  obtain ⟨t, s', he, ha, hq⟩ := hc s hs
  refine ⟨t, s', he, ha, ?_⟩
  have hW := hw s t s' hs he
  rw [post_regs hk] at hq ⊢
  refine hP _ _ _ _ (regArgs_length sig s hk) hq fun y hy => ?_
  have hk' : (sig.words 64).length ≤ VG.X86_64.argRegs.length := Nat.le_trans hk (by decide)
  cases ws with
  | nil => cases hy
  | cons y₀ ws =>
    simp only [Sig.writtenWithin, Abi.withConsts, abi, List.length_map, hk', ite_true] at hW
    exact hW y hy

/-- `P`, and the bytes of the last argument, `scratch` of `len` bytes, at
offset `w` and beyond unchanged. -/
def tail4 (w len : Nat) (P : Post4) : Post4 := fun a b c d m m' r =>
  P a b c d m m' r ∧ ∀ i, w ≤ i → i < len → m' (d + BitVec.ofNat 64 i) = m (d + BitVec.ofNat 64 i)

/-- `tail4`, of five arguments. -/
def tail5 (w len : Nat) (P : Post5) : Post5 := fun a b c d e m m' r =>
  P a b c d e m m' r ∧ ∀ i, w ≤ i → i < len → m' (e + BitVec.ofNat 64 i) = m (e + BitVec.ofNat 64 i)

/-- `tail4`, of six arguments. -/
def tail6 (w len : Nat) (P : Post6) : Post6 := fun a b c d e f m m' r =>
  P a b c d e f m m' r ∧ ∀ i, w ≤ i → i < len → m' (f + BitVec.ofNat 64 i) = m (f + BitVec.ofNat 64 i)

/-- The bytes of `scratch` from `w` on are unchanged: `w` is its length, or
the bound the code writes within. -/
theorem tail_bytes {m m' : Mem} {p : Addr} {w len : Nat} {ws : List (String × Nat)} {arrs : List (String × Region)}
    (harr : ("scratch", (⟨p, len⟩ : Region)) ∈ arrs) (hw : w = len ∨ ("scratch", w) ∈ ws)
    (hW : ∀ y ∈ ws, ∀ b ∈ arrs, b.1 = y.1 → ∀ i, y.2 ≤ i → i < b.2.len →
      m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) :
    ∀ i, w ≤ i → i < len → m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := by
  intro i h1 h2
  rcases hw with rfl | hy
  · omega
  · exact hW _ hy _ harr rfl i h1 h2

theorem tail4_of {P : Post4} {w len : Nat} {ws : List (String × Nat)} (params : List (String × Param))
    (harr : ∀ a b c d, ("scratch", (⟨d, len⟩ : Region)) ∈ Sig.arrays params [a, b, c, d])
    (hw : w = len ∨ ("scratch", w) ∈ ws) :
    ∀ vs m m' x, vs.length = 4 → Curry.apply [.addr, .addr, .addr, .addr] P vs m m' x →
      (∀ y ∈ ws, ∀ b ∈ Sig.arrays params vs, b.1 = y.1 → ∀ i, y.2 ≤ i → i < b.2.len →
        m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply [.addr, .addr, .addr, .addr] (tail4 w len P) vs m m' x := by
  intro vs m m' x hl h hW
  obtain ⟨a, b, c, d, rfl⟩ := vs4 hl
  have ht := tail_bytes (harr a b c d) hw hW
  exact ⟨h, ht⟩

theorem tail5_of {P : Post5} {w len : Nat} {ws : List (String × Nat)} (params : List (String × Param))
    (harr : ∀ a b c d e, ("scratch", (⟨e, len⟩ : Region)) ∈ Sig.arrays params [a, b, c, d, e])
    (hw : w = len ∨ ("scratch", w) ∈ ws) :
    ∀ vs m m' x, vs.length = 5 → Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m m' x →
      (∀ y ∈ ws, ∀ b ∈ Sig.arrays params vs, b.1 = y.1 → ∀ i, y.2 ≤ i → i < b.2.len →
        m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] (tail5 w len P) vs m m' x := by
  intro vs m m' x hl h hW
  obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hl
  have ht := tail_bytes (harr a b c d e) hw hW
  exact ⟨h, ht⟩

theorem tail6_of {P : Post6} {w len : Nat} {ws : List (String × Nat)} (params : List (String × Param))
    (harr : ∀ a b c d e f, ("scratch", (⟨f, len⟩ : Region)) ∈ Sig.arrays params [a, b, c, d, e, f])
    (hw : w = len ∨ ("scratch", w) ∈ ws) :
    ∀ vs m m' x, vs.length = 6 → Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m m' x →
      (∀ y ∈ ws, ∀ b ∈ Sig.arrays params vs, b.1 = y.1 → ∀ i, y.2 ≤ i → i < b.2.len →
        m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (tail6 w len P) vs m m' x := by
  intro vs m m' x hl h hW
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hl
  have ht := tail_bytes (harr a b c d e f) hw hW
  exact ⟨h, ht⟩

/-- Memories agreeing on `scratch`, of `len` bytes at `p`, agree on its
bytes from `w` on, and so on whether they are unchanged. -/
theorem tail_local {m₁ m₂ m' : Mem} {p : Addr} {w len : Nat} (hlen : len < 2 ^ 64)
    (hb : ∀ a, (⟨p, len⟩ : Region).Contains a 1 → m₁ a = m₂ a)
    (h : ∀ i, w ≤ i → i < len → m' (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ∀ i, w ≤ i → i < len → m' (p + BitVec.ofNat 64 i) = m₂ (p + BitVec.ofNat 64 i) := by
  intro i h1 h2
  rw [h i h1 h2]
  exact hb _ (Offset.contains_base _ (by omega) (by omega))

theorem tail4_local {P : Post4} {w len : Nat} (params : List (String × Param))
    (hbuf : ∀ a b c d, ((⟨d, len⟩ : Region), true) ∈ Sig.bufs params [a, b, c, d]) (hlen : len < 2 ^ 64)
    (hP : ∀ vs m₁ m₂ m' x, vs.length = 4 → (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr] P vs m₁ m' x → Curry.apply [.addr, .addr, .addr, .addr] P vs m₂ m' x) :
    ∀ vs m₁ m₂ m' x, vs.length = 4 → (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr] (tail4 w len P) vs m₁ m' x →
        Curry.apply [.addr, .addr, .addr, .addr] (tail4 w len P) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hl hb h
  have hP' := hP vs m₁ m₂ m' x hl hb
  obtain ⟨a, b, c, d, rfl⟩ := vs4 hl
  have ht := tail_local hlen (hb _ (hbuf a b c d)) h.2
  exact ⟨hP' h.1, ht⟩

theorem tail5_local {P : Post5} {w len : Nat} (params : List (String × Param))
    (hbuf : ∀ a b c d e, ((⟨e, len⟩ : Region), true) ∈ Sig.bufs params [a, b, c, d, e]) (hlen : len < 2 ^ 64)
    (hP : ∀ vs m₁ m₂ m' x, vs.length = 5 → (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m₁ m' x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m₂ m' x) :
    ∀ vs m₁ m₂ m' x, vs.length = 5 → (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] (tail5 w len P) vs m₁ m' x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr] (tail5 w len P) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hl hb h
  have hP' := hP vs m₁ m₂ m' x hl hb
  obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hl
  have ht := tail_local hlen (hb _ (hbuf a b c d e)) h.2
  exact ⟨hP' h.1, ht⟩

theorem tail6_local {P : Post6} {w len : Nat} (params : List (String × Param))
    (hbuf : ∀ a b c d e f, ((⟨f, len⟩ : Region), true) ∈ Sig.bufs params [a, b, c, d, e, f])
    (hlen : len < 2 ^ 64)
    (hP : ∀ vs m₁ m₂ m' x, vs.length = 6 → (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m₁ m' x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m₂ m' x) :
    ∀ vs m₁ m₂ m' x, vs.length = 6 → (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (tail6 w len P) vs m₁ m' x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (tail6 w len P) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hl hb h
  have hP' := hP vs m₁ m₂ m' x hl hb
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hl
  have ht := tail_local hlen (hb _ (hbuf a b c d e f)) h.2
  exact ⟨hP' h.1, ht⟩

/-- Memories on return agreeing on `scratch`, of `len` bytes at `p`, but its
first `w`, agree on whether its bytes from `w` on are unchanged. -/
theorem tail_out {m m₁ m₂ : Mem} {p : Addr} {w len : Nat} (hlen : len < 2 ^ 64)
    (hb : ∀ a, (⟨p, len⟩ : Region).Contains a 1 → ¬(⟨p, w⟩ : Region).Contains a 1 → m₁ a = m₂ a)
    (h : ∀ i, w ≤ i → i < len → m₁ (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    ∀ i, w ≤ i → i < len → m₂ (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := by
  intro i h1 h2
  rw [← h i h1 h2]
  refine (hb _ (Offset.contains_base _ (by omega) (by omega)) fun hc => ?_).symm
  simp only [Region.Contains] at hc
  rw [Mem.sub_ofNat_toNat p (by omega)] at hc
  omega

theorem tail4_out {P : Post4} {w len : Nat} (params : List (String × Param))
    (hbuf : ∀ a b c d, ((⟨d, len⟩ : Region), true) ∈ Sig.bufs params [a, b, c, d]) (hwl : w ≤ len)
    (hlen : len < 2 ^ 64)
    (hP : ∀ vs m m₁ m₂ x, vs.length = 4 →
      (Sig.bufs params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs params vs, b.1.Disjoint ⟨vs.getD 3 0, len⟩ → ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr] P vs m m₁ x → Curry.apply [.addr, .addr, .addr, .addr] P vs m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = 4 →
      (Sig.bufs params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → ¬(⟨vs.getD 3 0, w⟩ : Region).Contains a 1 →
        m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr] (tail4 w len P) vs m m₁ x →
        Curry.apply [.addr, .addr, .addr, .addr] (tail4 w len P) vs m m₂ x := by
  intro vs m m₁ m₂ x hl hpw hag h
  have hP' := hP vs m m₁ m₂ x hl hpw fun b hb hbA a ha =>
    hag b hb a ha fun hp => hbA a ha (Region.sub_prefix hwl a hp)
  obtain ⟨a, b, c, d, rfl⟩ := vs4 hl
  have ht := tail_out hlen (hag _ (hbuf a b c d)) h.2
  exact ⟨hP' h.1, ht⟩

theorem tail5_out {P : Post5} {w len : Nat} (params : List (String × Param))
    (hbuf : ∀ a b c d e, ((⟨e, len⟩ : Region), true) ∈ Sig.bufs params [a, b, c, d, e]) (hwl : w ≤ len)
    (hlen : len < 2 ^ 64)
    (hP : ∀ vs m m₁ m₂ x, vs.length = 5 →
      (Sig.bufs params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs params vs, b.1.Disjoint ⟨vs.getD 4 0, len⟩ → ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m m₁ x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = 5 →
      (Sig.bufs params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → ¬(⟨vs.getD 4 0, w⟩ : Region).Contains a 1 →
        m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] (tail5 w len P) vs m m₁ x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr] (tail5 w len P) vs m m₂ x := by
  intro vs m m₁ m₂ x hl hpw hag h
  have hP' := hP vs m m₁ m₂ x hl hpw fun b hb hbA a ha =>
    hag b hb a ha fun hp => hbA a ha (Region.sub_prefix hwl a hp)
  obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hl
  have ht := tail_out hlen (hag _ (hbuf a b c d e)) h.2
  exact ⟨hP' h.1, ht⟩

theorem tail6_out {P : Post6} {w len : Nat} (params : List (String × Param))
    (hbuf : ∀ a b c d e f, ((⟨f, len⟩ : Region), true) ∈ Sig.bufs params [a, b, c, d, e, f]) (hwl : w ≤ len)
    (hlen : len < 2 ^ 64)
    (hP : ∀ vs m m₁ m₂ x, vs.length = 6 →
      (Sig.bufs params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs params vs, b.1.Disjoint ⟨vs.getD 5 0, len⟩ → ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m m₁ x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = 6 →
      (Sig.bufs params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs params vs, ∀ a, b.1.Contains a 1 → ¬(⟨vs.getD 5 0, w⟩ : Region).Contains a 1 →
        m₁ a = m₂ a) →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (tail6 w len P) vs m m₁ x →
        Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (tail6 w len P) vs m m₂ x := by
  intro vs m m₁ m₂ x hl hpw hag h
  have hP' := hP vs m m₁ m₂ x hl hpw fun b hb hbA a ha =>
    hag b hb a ha fun hp => hbA a ha (Region.sub_prefix hwl a hp)
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hl
  have ht := tail_out hlen (hag _ (hbuf a b c d e f)) h.2
  exact ⟨hP' h.1, ht⟩

/-- With the first `w` bytes of `scratch` zero on return, `scrub4`. -/
theorem wipedTail4 (w len : Nat) (P : Post4) : ∀ vs m m' x, vs.length = 4 →
    Curry.apply [.addr, .addr, .addr, .addr] (tail4 w len P) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) w = Spec.Zeroize.zeros w →
      Curry.apply [.addr, .addr, .addr, .addr] (scrub4 len P) vs m m' x := by
  intro vs m m' x hl h hz
  obtain ⟨a, b, c, d, rfl⟩ := vs4 hl
  have ht := scrubbed_of_prefix hz h.2
  exact ⟨h.1, ht⟩

/-- With the first `w` bytes of `scratch` zero on return, `scrub5`. -/
theorem wipedTail5 (w len : Nat) (P : Post5) : ∀ vs m m' x, vs.length = 5 →
    Curry.apply [.addr, .addr, .addr, .addr, .addr] (tail5 w len P) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) w = Spec.Zeroize.zeros w →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] (scrub5 len P) vs m m' x := by
  intro vs m m' x hl h hz
  obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hl
  have ht := scrubbed_of_prefix hz h.2
  exact ⟨h.1, ht⟩

/-- With the first `w` bytes of `scratch` zero on return, `scrub6`. -/
theorem wipedTail6 (w len : Nat) (P : Post6) : ∀ vs m m' x, vs.length = 6 →
    Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (tail6 w len P) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) w = Spec.Zeroize.zeros w →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (scrub6 len P) vs m m' x := by
  intro vs m m' x hl h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hl
  have ht := scrubbed_of_prefix hz h.2
  exact ⟨h.1, ht⟩

theorem wiped1024_le (c : Callee4) : wiped1024 c ≤ 49152 := by unfold wiped1024; split <;> decide

theorem wipedEnc1024_le (c : Callee4) : wipedEnc1024 c ≤ 49152 := by unfold wipedEnc1024; split <;> decide

/-! ### ML-KEM-1024's code, with the bytes of `scratch` it does not write unchanged -/

theorem keyGen1024_tail (v : Sample4Impl) :
    Verified X86_64.target (keyGen1024 v.callee) (Spec.MlKem1024.keyGenSig.contract abi
      (post := tail4 (wiped1024 v.callee) 49152 (Scrubbed.keyGen1024Post abi.ptrBits)) (writeArgs := true)
      (stack := 32) (leak := some fun seed _ek _dk _scratch m =>
        Spec.MlKem.leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem1024 (Spec.Sha3.bytesAt m seed 32)))) :=
  Verified.tail_of_written (Proof.MlKem1024.X86_64.keyGen1024_verified v) (by decide)
    (Proof.MlKem1024.X86_64.keyGen1024_written v)
    (tail4_of _ (fun _ _ _ _ => by simp [Spec.MlKem1024.keyGenSig, Sig.arrays, Elem.size])
      (by
        by_cases hc : v.callee.s16.isSome <;>
          simp [wiped1024, Proof.MlKem1024.X86_64.written, hc]))

theorem encapsH1024_tail (v : Sample4Impl) :
    Verified X86_64.target (encapsH1024 v.callee) (Spec.MlKem1024.encapsHSig.contract abi
      (pre := fun ek h _msg _key _ct _scratch m =>
        Spec.Sha3.bytesAt m h 32 = Spec.MlKem.H (Spec.Sha3.bytesAt m ek 1568))
      (post := tail6 (wiped1024 v.callee) 49152 (Scrubbed.encapsH1024Post abi.ptrBits)) (writeArgs := true)
      (stack := 32) (leak := some fun ek _h _msg _key _ct _scratch m =>
        Spec.MlKem.leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (Spec.Sha3.bytesAt m ek 1568)))) :=
  Verified.tail_of_written (Proof.MlKem1024.X86_64.encapsH1024_verified v) (by decide)
    (Proof.MlKem1024.X86_64.encapsH1024_written v)
    (tail6_of _ (fun _ _ _ _ _ _ => by
        simp [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.arrays, Elem.size])
      (by
        by_cases hc : v.callee.s16.isSome <;>
          simp [wiped1024, Proof.MlKem1024.X86_64.written, hc]))

theorem encaps1024_tail (v : Sample4Impl) :
    Verified X86_64.target (encaps1024 v.callee) (Spec.MlKem1024.encapsSig.contract abi
      (post := tail5 (wipedEnc1024 v.callee) 49152 (Scrubbed.encaps1024Post abi.ptrBits)) (writeArgs := true)
      (stack := 32) (leak := some fun ek _msg _key _ct _scratch m =>
        Spec.MlKem.leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (Spec.Sha3.bytesAt m ek 1568)))) :=
  Verified.tail_of_written (Proof.MlKem1024.X86_64.encaps1024_verified v) (by decide)
    (Proof.MlKem1024.X86_64.encaps1024_written v)
    (tail5_of _ (fun _ _ _ _ _ => by simp [Spec.MlKem1024.encapsSig, Sig.arrays, Elem.size])
      (by
        by_cases hc : (v.callee.s16.isSome && v.callee.batchH16.isSome) = true <;>
          simp only [wipedEnc1024, Proof.MlKem1024.X86_64.writtenEnc, hc, ite_true, ite_false,
            List.mem_singleton, List.not_mem_nil, or_true, or_false, Bool.false_eq_true]))

theorem decaps1024_tail (v : Sample4Impl) :
    Verified X86_64.target (decaps1024 v.callee) (Spec.MlKem1024.decapsSig.contract abi
      (post := tail4 (wipedEnc1024 v.callee) 49152 (Scrubbed.decaps1024Post abi.ptrBits)) (writeArgs := true)
      (stack := 32) (leak := some fun dk _ct _key _scratch m =>
        Spec.MlKem.leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem1024 (Spec.Sha3.bytesAt m dk 3168)))) :=
  Verified.tail_of_written (Proof.MlKem1024.X86_64.decaps1024_verified v) (by decide)
    (Proof.MlKem1024.X86_64.decaps1024_written v)
    (tail4_of _ (fun _ _ _ _ => by simp [Spec.MlKem1024.decapsSig, Sig.arrays, Elem.size])
      (by
        by_cases hc : (v.callee.s16.isSome && v.callee.batchH16.isSome) = true <;>
          simp only [wipedEnc1024, Proof.MlKem1024.X86_64.writtenEnc, hc, ite_true, ite_false,
            List.mem_singleton, List.not_mem_nil, or_true, or_false, Bool.false_eq_true]))

/-! ## The functions -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGenW_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (keyGenW v.callee v.suffix z.name z.code) (Scrubbed.keyGenContract X86_64.abi 56) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) (keyGen_verified v) z.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (keyGen_spSafe v) (keyGen_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    ⟨keyGenSat, by
      sig_pre [Spec.MlKem.keyGenSig, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

theorem keyGenW_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (keyGenW v.callee v.suffix z.name z.code) (Spec.MlKem.keyGenContract X86_64.abi 56) :=
  Scrubbed.Verified.keyGen_of_scrubbed (keyGenW_scrubbed v z)

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsHW_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encapsHW v.callee v.suffix z.name z.code) (Scrubbed.encapsHContract X86_64.abi 56) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) (encapsH_verified v) z.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (encapsH_spSafe v) (encapsH_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    ⟨encapsHSat 1184 1088 32768, by
      sig_pre [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | exact encapsHSat_h (ekLen := 1184) (ctLen := 1088) (scr := 32768) (by decide) | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

theorem encapsHW_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encapsHW v.callee v.suffix z.name z.code) (Spec.MlKem.encapsHContract X86_64.abi 56) :=
  Scrubbed.Verified.encapsH_of_scrubbed (encapsHW_scrubbed v z)

/-- `vg_mlkem768_encaps`. -/
theorem encapsW_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encapsW v.callee v.suffix z.name z.code) (Scrubbed.encapsContract X86_64.abi 56) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) (encaps_verified v) z.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (encaps_spSafe v) (encaps_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    ⟨encapsSat 1184 1088 32768, by
      sig_pre [Spec.MlKem.encapsSig, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

theorem encapsW_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encapsW v.callee v.suffix z.name z.code) (Spec.MlKem.encapsContract X86_64.abi 56) :=
  Scrubbed.Verified.encaps_of_scrubbed (encapsW_scrubbed v z)

/-- `vg_mlkem768_decaps`. -/
theorem decapsW_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (decapsW v.callee v.suffix z.name z.code) (Scrubbed.decapsContract X86_64.abi 56) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) (decaps_verified v) z.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (decaps_spSafe v) (decaps_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    ⟨decapsSat, by
      sig_pre [Spec.MlKem.decapsSig, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])

theorem decapsW_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (decapsW v.callee v.suffix z.name z.code) (Spec.MlKem.decapsContract X86_64.abi 56) :=
  Scrubbed.Verified.decaps_of_scrubbed (decapsW_scrubbed v z)

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024W_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (keyGen1024W v.callee v.suffix z.name z.code) (Scrubbed.keyGen1024Contract X86_64.abi 56) :=
  Verified.callWipeTail' (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) (keyGen1024_tail v) z.verified
    (by decide) (by decide) rfl rfl (by unfold wiped1024; split <;> decide) (by unfold wiped1024; split <;> decide) (by decide) (keyGen1024_spSafe v) (keyGen1024_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (tail4_local _ (fun _ _ _ _ => by simp [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (by decide)
      (by
        intro vs m₁ m₂ m' x hlen hb h
        obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
        simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.keyGen1024Post] at h ⊢
        rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
          show a + 32 = a + BitVec.ofNat 64 32 from rfl,
          ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
        exact h))
    (tail4_out _ (fun _ _ _ _ => by simp [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (wiped1024_le _) (by decide)
      (by
        intro vs m m₁ m₂ x hlen hpw hb h
        obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
        simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.keyGen1024Post] at h ⊢
        rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 1568) (by decide),
          ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 3168) (by decide)]
        exact h))
    (wipedTail4 _ _ _)
    ⟨MlKem1024.X86_64.keyGen1024Sat, by
      sig_pre [Spec.MlKem1024.keyGenSig, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

theorem keyGen1024W_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (keyGen1024W v.callee v.suffix z.name z.code) (Spec.MlKem1024.keyGenContract X86_64.abi 56) :=
  Scrubbed.Verified.keyGen1024_of_scrubbed (keyGen1024W_scrubbed v z)

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024W_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encapsH1024W v.callee v.suffix z.name z.code) (Scrubbed.encapsH1024Contract X86_64.abi 56) :=
  Verified.callWipeTail' (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) (encapsH1024_tail v) z.verified
    (by decide) (by decide) rfl rfl (by unfold wiped1024; split <;> decide) (by unfold wiped1024; split <;> decide) (by decide) (encapsH1024_spSafe v) (encapsH1024_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (tail6_local _ (fun _ _ _ _ _ _ => by simp [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (by decide)
      (by
        intro vs m₁ m₂ m' x hlen hb h
        obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
        simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.encapsH1024Post] at h ⊢
        rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
          ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
        exact h))
    (tail6_out _ (fun _ _ _ _ _ _ => by simp [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (wiped1024_le _) (by decide)
      (by
        intro vs m m₁ m₂ x hlen hpw hb h
        obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
        simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.encapsH1024Post] at h ⊢
        rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 32) (by decide),
          ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 1568) (by decide)]
        exact h))
    (wipedTail6 _ _ _)
    ⟨encapsHSat 1568 1568 49152, by
      sig_pre [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | exact encapsHSat_h (ekLen := 1568) (ctLen := 1568) (scr := 49152) (by decide) | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

theorem encapsH1024W_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encapsH1024W v.callee v.suffix z.name z.code) (Spec.MlKem1024.encapsHContract X86_64.abi 56) :=
  Scrubbed.Verified.encapsH1024_of_scrubbed (encapsH1024W_scrubbed v z)

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024W_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encaps1024W v.callee v.suffix z.name z.code) (Scrubbed.encaps1024Contract X86_64.abi 56) :=
  Verified.callWipeTail' (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) (encaps1024_tail v) z.verified
    (by decide) (by decide) rfl rfl (by unfold wipedEnc1024; split <;> decide) (by unfold wipedEnc1024; split <;> decide) (by decide) (encaps1024_spSafe v) (encaps1024_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (tail5_local _ (fun _ _ _ _ _ => by simp [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (by decide)
      (by
        intro vs m₁ m₂ m' x hlen hb h
        obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
        simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.encaps1024Post] at h ⊢
        rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
          ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
        exact h))
    (tail5_out _ (fun _ _ _ _ _ => by simp [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (wipedEnc1024_le _) (by decide)
      (by
        intro vs m m₁ m₂ x hlen hpw hb h
        obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
        simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.encaps1024Post] at h ⊢
        rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 32) (by decide),
          ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 1568) (by decide)]
        exact h))
    (wipedTail5 _ _ _)
    ⟨encapsSat 1568 1568 49152, by
      sig_pre [Spec.MlKem1024.encapsSig, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

theorem encaps1024W_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (encaps1024W v.callee v.suffix z.name z.code) (Spec.MlKem1024.encapsContract X86_64.abi 56) :=
  Scrubbed.Verified.encaps1024_of_scrubbed (encaps1024W_scrubbed v z)

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024W_scrubbed (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (decaps1024W v.callee v.suffix z.name z.code) (Scrubbed.decaps1024Contract X86_64.abi 56) :=
  Verified.callWipeTail' (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) (decaps1024_tail v) z.verified
    (by decide) (by decide) rfl rfl (by unfold wipedEnc1024; split <;> decide) (by unfold wipedEnc1024; split <;> decide) (by decide) (decaps1024_spSafe v) (decaps1024_xd v)
    z.spSafe (by rw [z.xd]) (by decide)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (tail4_local _ (fun _ _ _ _ => by simp [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (by decide)
      (by
        intro vs m₁ m₂ m' x hlen hb h
        obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
        simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.decaps1024Post] at h ⊢
        rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
          ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
        exact h))
    (tail4_out _ (fun _ _ _ _ => by simp [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, Elem.size]) (wipedEnc1024_le _) (by decide)
      (by
        intro vs m m₁ m₂ x hlen hpw hb h
        obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
        simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
        change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
        dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.decaps1024Post] at h ⊢
        rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide) (n := 32) (by decide)]
        exact h))
    (wipedTail4 _ _ _)
    ⟨MlKem1024.X86_64.decaps1024Sat, by
      sig_pre [Spec.MlKem1024.decapsSig, X86_64.abi, VG.X86_64.argRegs]
      sig_and_intros
      all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)⟩
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ =
        Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])

theorem decaps1024W_verified (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    Verified X86_64.target (decaps1024W v.callee v.suffix z.name z.code) (Spec.MlKem1024.decapsContract X86_64.abi 56) :=
  Scrubbed.Verified.decaps1024_of_scrubbed (decaps1024W_scrubbed v z)


/-! ## The stack pointer -/

theorem keyGenW_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (keyGenW v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (keyGen_spSafe v) z.spSafe

theorem encapsHW_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (encapsHW v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (encapsH_spSafe v) z.spSafe

theorem encapsW_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (encapsW v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (encaps_spSafe v) z.spSafe

theorem decapsW_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (decapsW v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (decaps_spSafe v) z.spSafe

theorem keyGen1024W_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (keyGen1024W v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (keyGen1024_spSafe v) z.spSafe

theorem encapsH1024W_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (encapsH1024W v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (encapsH1024_spSafe v) z.spSafe

theorem encaps1024W_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (encaps1024W v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (encaps1024_spSafe v) z.spSafe

theorem decaps1024W_spSafe (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) :
    (decaps1024W v.callee v.suffix z.name z.code).all (fun i => !X86_64.isa.writesSp i) = true :=
  callWipe_spSafe (decaps1024_spSafe v) z.spSafe

/-! ## The instances -/

/-- Whether the functions are not emitted with the implementations `v` and
`z`: an implementation of `vg_mlkem_sample_ntt4` that needs CPU features
calls only an implementation of `vg_zeroize` that needs some of them (every
one but the baseline needs AVX, which `vg_zeroize_avx` needs). -/
def Wipe.skip (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) : Bool :=
  !v.features.isEmpty && !z.features.any v.features.contains

/-- What the names of the functions end with: `v`'s suffix, or, with the
baseline of `vg_mlkem_sample_ntt4`, `z`'s. -/
def Wipe.suffix (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) : String :=
  if v.features.isEmpty then z.suffix else v.suffix

/-- The CPU features the functions need: those of `v` and `z`. -/
def Wipe.features (v : Sample4Impl) (z : Proof.Zeroize.X86_64.ZeroizeImpl) : List String :=
  v.features ++ z.features.filter (!v.features.contains ·)

end VG.Proof.MlKem.X86_64

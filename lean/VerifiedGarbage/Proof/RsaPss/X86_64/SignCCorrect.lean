module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.ByIdx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignFrame

/-!
# RSASSA-PSS signing on x86-64, around the encoding: correctness

`signC_ok`: from the entry state, `signC` refuses a modulus whose first
byte is zero, computes `emBits`, calls `encode` for the hash function of
the table `hash` (by its index, `byIdx`) for the encoding at
`scratch + oEm + lo` after a zero byte, and, if it fits, the private-key
operation on those `k` bytes, which leaves `out` and `rax` as
`RsaPss.sign` says (`sign_encode₂`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {tsH tsG : List FnTable}

/-- `encode`'s return value, tested. -/
theorem test32_ok (u : State) :
    WP isa (.block [.alu32 .test .rax (.reg .rax)]) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.zf = some (decide ((u.gpr .rax).setWidth 32 = 0)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧
      u'.zf = some (decide ((u.gpr .rax).setWidth 32 = 0))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun []
  rw [BitVec.and_self, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

/-- `lo = k - emLen` is 0 or 1. -/
theorem lo_le {k x : Nat} (hx : Nat.log2 x < 8) (hk : 1 ≤ k) : k - Spec.RsaPss.emLength (ebV k x) ≤ 1 := by
  unfold Spec.RsaPss.emLength ebV; omega

/-- The bytes the private-key operation reads: a zero byte (if `lo = 1`),
then the encoding. -/
theorem em_input {m : Mem} {S : Addr} {V : Nat → Byte} {lo el k : Nat} {e : List Byte} (hk : lo + el = k)
    (hlo : lo ≤ 1) (he : Spec.Rsa.bytesAt m (off S (oEm + lo)) el = e) :
    (List.range k).map (fun i => (fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then m (off S o)
      else upd V oEm 0 o) (oEm + i)) = Spec.RsaPss.zeros lo ++ e := by
  subst he
  have c1 : oEm = 2560 := rfl
  have c3 : oEnc = 4096 := rfl
  apply List.ext_getElem
  · simp [Spec.RsaPss.zeros, Spec.Rsa.bytesAt]; omega
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < lo
  · rw [ifn (fun ⟨p, hp, a, b⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only at a b <;> omega)]
    rw [List.getElem_append_left (by simp [Spec.RsaPss.zeros]; omega)]
    simp only [upd, Spec.RsaPss.zeros, List.getElem_replicate]
    rw [ifp (by omega)]
  · rw [ifp ⟨_, List.mem_cons_self .., by dsimp only; omega, by dsimp only; omega⟩]
    rw [List.getElem_append_right (by simp [Spec.RsaPss.zeros]; omega)]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Spec.RsaPss.zeros, List.length_replicate,
      off_plus]
    congr 2; omega

/-- The slots after `idxSlot`. -/
def proW1 (s : State) : Nat → BitVec 64 := upd (proW s) 47 (s.mem.readW (off (stackArg s 16) 40) 64)

/-- The table `hash` to `r11`, the flags kept. -/
theorem r11Arg_ok {s u : State} (hp : SPre tsH tsG s) (hsp : u.gpr .rsp = fb s) (hrd : u.rd = s.rd)
    (hA : ArgsKept s u.mem) :
    WP isa (.block [.mov .r11 (.mem (arg 16))]) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r11 = stackArg s 16 ∧ u'.zf = u.zf := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * 16)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 144⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s 16 = stackArgAddr s 0 + BitVec.ofNat 64 (8 * 16) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact Offset.contains_base _ (by omega_using []) (by omega_using [])
  have hv : u.mem.readW (off (fb s) (frameBytes + 8 + 8 * 16)) 64 = stackArg s 16 := by
    rw [argAddr]; exact hA 16 (by decide)
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = stackArg s 16 ∧ u'.zf = u.zf) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [arg, ea_sp, hsp, hin, hv]

/-- The index of the table `hash`'s hash function to its slot, the flags
kept. -/
theorem idxSlot_ok {s u : State} (hp : SPre tsH tsG s) (L : Lay u (fb s) (stackArg s 14)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 14) V W) (hrd : u.rd = s.rd)
    (hM : Frame (wrR s) s.mem u.mem) (h11 : u.gpr .r11 = stackArg s 16) :
    WP isa (.block idxSlot) u fun u' => Lay u' (fb s) (stackArg s 14) ∧ Keep [.r11] u u' ∧
      Rep u'.mem (fb s) (stackArg s 14) V (upd W 47 (s.mem.readW (off (stackArg s 16) 40) 64)) ∧ u'.zf = u.zf ∧
      Frame (wrR s) s.mem u'.mem := by
  have hw := hp.wTH
  have G' := L.geo
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 16) 40) 8 :=
    ⟨⟨stackArg s 16, 88⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩
  have R1 := R.wf G' (k := 47) (by decide) (s.mem.readW (off (stackArg s 16) 40) 64)
  rw [show off (fb s) (8 * 47) = off (fb s) sIdx from rfl] at R1
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) sIdx)
      (s.mem.readW (off (stackArg s 16) 40) 64) ∧ u'.zf = u.zf) ?_ rfl) fun u' ⟨⟨hm, hz⟩, k⟩ => ?_
  · xrun [idxSlot, ea_at, ea_sp, L.rsp, h11, hin, idx_read hp hM, L.st (d := sIdx) (by decide)]
  have R' := hm ▸ R1
  refine ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, R', hz, ?_⟩
  rw [hm]
  exact hM.trans ((frame_w hp (Frame.refl _ _) (d := sIdx) (by decide) _).sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩)

/-- The index to `r11`. -/
theorem idxLoad_ok {s u : State} (L : Lay u (fb s) (stackArg s 14)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) (stackArg s 14) V W) :
    WP isa (.block idxLoad) u fun u' => Keep [.r11] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r11 = W 47 := by
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .r11 = W 47) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [idxLoad, ea_sp, L.rsp, L.ld (d := sIdx) (by decide), R.rd (d := sIdx) 47 rfl (by decide)]

/-- `emBits`, then `encode`'s arguments but the tables. -/
theorem encPrep_ok {s u : State} (L : Lay u (fb s) (stackArg s 14)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem (fb s) (stackArg s 14) V W) (h17 : W 17 = s.gpr .rcx) (h22 : W 22 = stackArg s 15)
    (h37 : W 37 = stackArg s 10) (h39 : W 39 = stackArg s 12) (h40 : W 40 = stackArg s 13)
    (hk1 : 1 ≤ (s.gpr .rcx).toNat)
    (hk2 : (s.gpr .rcx).toNat ≤ 1024) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block (emBitsB ++ (encA1 ++ encA2 ++ encA3))) u fun u' => Lay u' (fb s) (stackArg s 14) ∧
      Keep [.rdx, .rax, .r8, .rdi, .rax, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Rep u'.mem (fb s) (stackArg s 14) (upd V oEm 0)
        (upd (upd (upd (upd (upd W 27 (BitVec.ofNat 64 (ebV (s.gpr .rcx).toNat x))) 28
          (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)))) 26
          (BitVec.ofNat 64 ((s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)))) 0
          (off (stackArg s 14) oEnc)) 1 (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8))) ∧
      u'.gpr .rdi = off (stackArg s 14) (oEm + ((s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))) ∧
      u'.gpr .rsi = BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x)) ∧
      u'.gpr .rdx = stackArg s 10 ∧ u'.gpr .rcx = stackArg s 12 ∧ u'.gpr .r8 = stackArg s 13 ∧
      u'.gpr .r9 = BitVec.ofNat 64 (ebV (s.gpr .rcx).toNat x) := by
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok L R (k := (s.gpr .rcx).toNat) (x := x)
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk1 hk2 hx h0 hax) fun t ⟨L3, k3, R3⟩ => ?_
  exact WP.mono (encArgs3_ok L3 R3 (lo := (s.gpr .rcx).toNat - Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))
    (eb := ebV (s.gpr .rcx).toNat x) (el := Spec.RsaPss.emLength (ebV (s.gpr .rcx).toNat x))
    (dig := stackArg s 10) (q := stackArg s 12) (sl := stackArg s 13) (sw := stackArg s 15)
    (by simp [upd, h22]) (by simp [upd]) (by simp [upd]) (by simp [upd]) (by simp [upd, h37])
    (by simp [upd, h39]) (by simp [upd, h40]))
    fun t' ⟨L4, k4, R4, a, b, c, d, e, f⟩ => ⟨L4, k3.trans k4, R4, a, b, c, d, e, f⟩

theorem signC_ok {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {privN : String} {privC : Prog isa}
    (hspE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g)) (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) {s : State}
    (h : (signK tsH tsG).pre s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} (E : ESel f g s i T Hs Gs) :
    WP isa (Impl.RsaPss.X86_64.signC f g privN privC) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (signK tsH tsG).post s s' ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := SPre.of tsH tsG h
  have hF := fb_toNat hp
  have hk1 := hp.k1; have hk2 := hp.k2
  have hHl : Hs.len = T.H.D := ((hp.hdl Hs E.hH).symm.trans E.hD.symm)
  refine wp_frame (by have := hp.sp1; unfold signStack Rsa.X86_64.stackBytes frameBytes at *; omega_arith) ?_
  rw [signCBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_mxs (by decide) (signPro_ok hp)
    fun t1 ⟨k1, L1, R1, f1⟩ sy1 hx1 => ?_
  refine WP.mono_mxs (by decide) (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1))
    fun t2 ⟨k2, hm2, hax2, hz2⟩ sy2 hx2 => ?_
  have L2 : Lay t2 (fb s) (stackArg s 14) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have hM2 : Frame (wrR s) s.mem t2.mem := hm2 ▸ frame_wrR f1
  refine WP.mono_mxs (by decide) (r11Arg_ok hp L2.rsp (k2.2.1.trans k1.2.1) (argsKept_of hp hM2))
    fun t2' ⟨k2', hm2', h11, hz2'⟩ sy2' hx2' => ?_
  have L2' : Lay t2' (fb s) (stackArg s 14) := L2.congr (k2'.gpr (by decide)) k2'.2.2 (by rw [hm2'])
  refine WP.seq (WP.mono_mxs (by decide) (idxSlot_ok hp L2' (hm2' ▸ hm2 ▸ R1)
      (k2'.2.1.trans (k2.2.1.trans k1.2.1)) (hm2' ▸ hM2) h11)
    fun t3 ⟨L3, k3, R3, hz3, hM3⟩ sy3 hx3 => ?_)
  have hw3 : t3.wr = frR s :: s.wr := k3.2.2.trans (k2'.2.2.trans (k2.2.2.trans k1.2.2))
  have hrd3 : t3.rd = s.rd := k3.2.1.trans (k2'.2.1.trans (k2.2.1.trans k1.2.1))
  have hsy3 : t3.syms = s.syms := sy3.trans (sy2'.trans (sy2.trans sy1))
  have hcs3 : ∀ r ∈ [Reg.r13, .r14, .r15], t3.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.r11] ∧ r ∉ [Reg.rsi, .rax] ∧ r ∉ [Reg.rax] := by
      simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k3.gpr this.1, k2'.gpr this.1, k2.gpr this.2.1, k1.gpr this.2.2]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  have hax3 : t3.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), hax2]
  refine WP.seq (WP.mono (Q := SDone s) ?_ fun t D => restore_ok hp D)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdx) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdx + 1) ((s.gpr .rcx).toNat - 1) with hrest
  have hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega_arith)
  have hrl : rest.length = (s.gpr .rcx).toNat - 1 := by simp [hrest, Spec.Rsa.bytesAt]
  have hHs : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
      Spec.HashTable.hashAt 64 s.mem (stackArg s 17) = some G → H = Hs ∧ G = Gs := fun H G a b =>
    ⟨Option.some.inj (a.symm.trans E.hH), Option.some.inj (b.symm.trans E.hG)⟩
  have hx3' : t3.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx3, hx2', hx2, hx1]; rfl
  refine WP.ite (M := isa) _ (show isa.eval .e t3 = _ by rw [show isa.eval .e t3 = t3.zf from rfl, hz3, hz2', hz2])
    (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    have h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine fail_done hp L3 R3 hw3 hcs3 (by simp [proW, upd]) (by simp [proW, upd]) (by simp [proW, upd])
      (by simp [proW, upd]) (by simp [proW, upd]) (fun H G _ _ => ?_) hx3'
    rw [signOut, hnB, h0]; exact RsaPss.sign_zero₂ ..
  rw [decide_eq_false_iff_not] at hb
  have h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  have hl8 := RsaPss.log2_lt8 n₀
  set k := (s.gpr .rcx).toNat with hk
  set eb := ebV k n₀.toNat with heb_def
  set el := Spec.RsaPss.emLength eb with hel_def
  set lo := k - el with hlo_def
  have hlo : lo ≤ 1 := lo_le hl8 (by omega_arith)
  have heb : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) k)) - 1 = eb := by
    rw [hnB, RsaPss.emBits_eq rest h0, hrl]; rfl
  have heb1 : 1 ≤ eb := by rw [heb_def]; unfold ebV; omega_arith
  have heb2 : eb ≤ Proof.RsaPss.maxEmBits := by
    rw [heb_def]; unfold ebV Proof.RsaPss.maxEmBits; omega_arith
  have hlok : lo + el = k := by
    rw [hlo_def, hel_def, heb_def]; unfold Spec.RsaPss.emLength ebV; omega_arith
  -- `emBits`, `encode`'s arguments, and the index.
  have eA : emBitsB ++ encArgs ++ idxLoad = emBitsB ++ (encA1 ++ encA2 ++ encA3) ++ (encA4 ++ idxLoad) := by
    simp only [encArgs_eq, List.append_assoc]
  refine WP.seq ?_
  rw [eA, WP.block_append_iff]
  refine WP.mono_mxs (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encPrep_ok L3 R3 (by simp [proW, upd]) (by simp [proW, upd]) (by simp [proW, upd])
      (by simp [proW, upd]) (by simp [proW, upd]) (by omega_arith) hk2 n₀.isLt hb hax3))
    fun t4 ⟨⟨L4, k4, R4, h4di, h4si, h4dx, h4cx, h48, h49⟩, f4⟩ sy4 hx4 => ?_
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans hw3
  have hrd4 : t4.rd = s.rd := k4.2.1.trans hrd3
  have hM4 : Frame (wrR s) s.mem t4.mem := frame_keep hp hw3 L3.rsp hM3 f4
  rw [WP.block_append_iff]
  refine WP.mono_mxs (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encA4_ok hp L4 R4 hrd4 (argsKept_of hp hM4)))
    fun t5 ⟨⟨L5, k5, R5⟩, f5⟩ sy5 hx5 => ?_
  have hM5 : Frame (wrR s) s.mem t5.mem := frame_keep hp hw4 L4.rsp hM4 f5
  refine WP.mono_mxs (by decide) (idxLoad_ok L5 R5)
    fun t6 ⟨k6, hm6, h116⟩ sy6 hx6 => ?_
  set W6 := upd (upd (upd (upd (upd (upd (upd (proW1 s) 27 (BitVec.ofNat 64 eb)) 28 (BitVec.ofNat 64 el)) 26
    (BitVec.ofNat 64 lo)) 0 (off (stackArg s 14) oEnc)) 1 (stackArg s 15 - BitVec.ofNat 64 (oEnc / 8))) 2
    (stackArg s 16)) 3 (stackArg s 17) with hW6
  have R6 : Rep t6.mem (fb s) (stackArg s 14) (upd (fun o => s.mem (off (stackArg s 14) o)) oEm 0) W6 := hm6 ▸ R5
  have L6 : Lay t6 (fb s) (stackArg s 14) := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  have hi11 : t6.gpr .r11 = BitVec.ofNat 64 i := by
    rw [h116, ← E.idx]; simp [upd]
  have hw6 : t6.wr = frR s :: s.wr := k6.2.2.trans (k5.2.2.trans hw4)
  have hrd6 : t6.rd = s.rd := k6.2.1.trans (k5.2.1.trans hrd4)
  have hM6 : Frame (wrR s) s.mem t6.mem := hm6 ▸ hM5
  have hsy6 : t6.syms = s.syms := sy6.trans (sy5.trans (sy4.trans hsy3))
  have g46 : ∀ r, r ∉ [Reg.rax, .r11] → t6.gpr r = t4.gpr r := fun r hr => by
    rw [k6.gpr (fun h => hr (by simp at h ⊢; exact .inr h)), k5.gpr (fun h => hr (by simp at h ⊢; exact .inl h))]
  have hx6' : t6.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx6, hx5, hx4]; exact hx3'
  -- The index chooses `encode`.
  refine WP.seq (byIdx_wp (i := i) E.mem cmpOk_idxs hi11 fun t7 k7 hm7 sy7 hx7 => ?_)
  have R7 : Rep t7.mem (fb s) (stackArg s 14) (upd (fun o => s.mem (off (stackArg s 14) o)) oEm 0) W6 := hm7 ▸ R6
  have g7 : ∀ r, t7.gpr r = t6.gpr r := fun r => k7.gpr (List.not_mem_nil)
  have EA : EncAt T s t7 lo eb el :=
    { sp := (g7 _).trans L6.rsp, rd := k7.2.1.trans hrd6, wr := k7.2.2.trans hw6, M := hm7 ▸ hM6,
      sy := sy7.trans hsy6, w0 := (R7.fr 0 (by decide)).trans (by simp [hW6, upd]),
      w1 := (R7.fr 1 (by decide)).trans (by simp [hW6, upd]), w2 := (R7.fr 2 (by decide)).trans (by simp [hW6, upd]),
      w3 := (R7.fr 3 (by decide)).trans (by simp [hW6, upd]),
      di := (g7 _).trans ((g46 _ (by decide)).trans h4di), si := (g7 _).trans ((g46 _ (by decide)).trans h4si),
      dx := (g7 _).trans ((g46 _ (by decide)).trans h4dx), cx := (g7 _).trans ((g46 _ (by decide)).trans h4cx),
      r8 := (g7 _).trans ((g46 _ (by decide)).trans h48), r9 := (g7 _).trans ((g46 _ (by decide)).trans h49),
      lo1 := hlo, eb1 := heb1, eb2 := heb2, hel := rfl, hD := E.hD, tabs := E.tabs }
  refine WP.mono (enc_call (Hs := Hs) (Gs := Gs) E.ok (hspE i E.mem) (hdE i E.mem) hp EA R7)
    fun t8 ⟨rd8, wr8, cs8, mx8, hM8, sy8, R8, hE⟩ => ?_
  set V8 := fun o => if inR [(oEm + lo, el), (oEnc, oRsa - oEnc)] o then t8.mem (off (stackArg s 14) o)
    else upd (fun o => s.mem (off (stackArg s 14) o)) oEm 0 o with hV8
  have L8 : Lay t8 (fb s) (stackArg s 14) := (L6.congr ((g7 _)) (k7.2.2) (by rw [hm7])).of_rep' R7 R8 rfl
    (cs8 .rsp (by decide)) wr8
  -- Its result, tested.
  refine WP.seq (WP.mono_mx (by decide) (test32_ok t8) fun t9 ⟨k9, hm9, hz9⟩ hx9 => ?_)
  have L9 : Lay t9 (fb s) (stackArg s 14) := L8.congr (k9.gpr (by decide)) k9.2.2 (by rw [hm9])
  have R9 : Rep t9.mem (fb s) (stackArg s 14) V8 W6 := by rw [hm9]; exact R8
  have hM9 : Frame (wrR s) s.mem t9.mem := by rw [hm9]; exact hM8
  have hw9 : t9.wr = frR s :: s.wr := k9.2.2.trans (wr8.trans (k7.2.2.trans hw6))
  have hrd9 : t9.rd = s.rd := k9.2.1.trans (rd8.trans (k7.2.1.trans hrd6))
  have hcs9 : ∀ r ∈ [Reg.r13, .r14, .r15], t9.gpr r = s.gpr r := fun r hr => by
    have h1 : r ∈ calleeSaved := by simp at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [k9.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs8 r h1, g7,
      g46 r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp),
      k4.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs3 r hr]
  have hmx9 : t9.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [hx9, mx8, hx7]; exact hx6'
  refine WP.ite (M := isa) _ (show isa.eval .e t9 = _ from hz9) (fun hb9 => ?_) (fun hb9 => ?_)
  · -- No encoding: refused.
    rw [decide_eq_true_eq] at hb9
    refine fail_done hp L9 R9 hw9 hcs9 (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (fun H G a b => ?_) hmx9
    obtain ⟨rfl, rfl⟩ := hHs H G a b
    rw [signOut, RsaPss.sign_encode₂ H G heb, hHl]
    cases he : Spec.RsaPss.encode H G (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb with
    | none => rfl
    | some e =>
      rw [he] at hE
      obtain ⟨h1, -⟩ := hE
      exact absurd (hb9.symm.trans h1) (by decide)
  rw [decide_eq_false_iff_not] at hb9
  obtain ⟨e, he, hbytes⟩ : ∃ e, Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb = some e ∧
      Spec.Rsa.bytesAt t8.mem (off (stackArg s 14) (oEm + lo)) el = e := by
    cases he : Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 10) T.H.D)
      (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat) eb with
    | none => rw [he] at hE; exact absurd hE hb9
    | some e => rw [he] at hE; exact ⟨e, rfl, hE.2⟩
  -- The private-key operation's arguments.
  refine WP.seq (WP.mono_mx (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (privArgs_ok hp L9 hrd9 (argsKept_of hp hM9) R9 (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd]) (by simp [hW6, proW1, proW, upd])
      (by simp [hW6, proW1, proW, upd])))
    fun u2 ⟨⟨k10, L10, ⟨W2, R10, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f10⟩ hx10 => ?_)
  have hw10 : u2.wr = frR s :: s.wr := k10.2.2.trans hw9
  have hM10 := frame_keep hp hw9 L9.rsp hM9 f10
  -- The call.
  refine WP.mono (priv_call hv hspC hdC hp L10.rsp (k10.2.1.trans hrd9) hw10 hM10
    (fun i hi => (R10.fr i (by unfold nW frameBytes; omega_arith)).trans (hW2a i hi)) h2di h2si h2dx h2cx h2r8 h2r9)
    fun u3 ⟨rd3, wr3, cs3, mx3, _, hk3, hout3⟩ => ?_
  have R3' : Rep u3.mem (fb s) (stackArg s 14) V8 W2 := R10.of_keep L10.geo fun x hx => hk3 x hx
  have L3' : Lay u3 (fb s) (stackArg s 14) := L10.of_rep' R10 R3' rfl (cs3 .rsp (by decide)) wr3
  have w : ∀ j, 40 < j → j < nW → W2 j = proW1 s j := fun j h hj => by
    rw [hW2b j hj (by omega_arith)]; simp only [hW6, upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith),
      ifn (by omega_arith), ifn (by omega_arith)]
  refine ⟨L3', wr3.trans hw10, fun r hr => ?_, ?_, ?_, ?_, fun H G a b => ?_, by rw [mx3, hx10]; exact hmx9⟩
  · have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
    have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
    rw [cs3 r h1, k10.gpr h2, hcs9 r hr]
  · rw [R3'.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide)]; simp [proW1, proW, upd]
  · rw [R3'.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide)]; simp [proW1, proW, upd]
  · rw [R3'.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide)]; simp [proW1, proW, upd]
  · obtain ⟨rfl, rfl⟩ := hHs H G a b
    have hem : Spec.Rsa.bytesAt u2.mem (off (stackArg s 14) oEm) k = Spec.RsaPss.zeros lo ++ e := by
      rw [bytesAt_off, List.map_congr_left fun i hi => R10.scr _ (by have := List.mem_range.mp hi; unfold oEm oRsa; omega_arith)]
      exact em_input hlok hlo hbytes
    rw [hem] at hout3
    rw [signOut, RsaPss.sign_encode₂ H G heb, hHl, he, bytesAt_length]
    exact hout3

end VG.Proof.RsaPss.X86_64

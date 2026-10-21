module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
public import VerifiedGarbage.Impl.AesGcm.AArch64.Tail
public import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Bytes
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on AArch64: counter mode over a piece, the last bytes in place

Untrusted: everything here is checked by Lean. `Tail.cryptAlT` is
`cryptAl` with the keystream block zeroed by one store (`crSeg2T_ok`) and,
when the text is at least a block long, its last bytes XORed in the 16
bytes that end it (`ksTail_ok`), which leaves the memory `crTail` leaves
(`Tail.ks_mem`), so the same `CrOut` (`crOut_of_xor`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.Tail VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A zero 16-byte store, as bytes. -/
theorem write_zero16 (m : Mem) (a : Addr) :
    m.write a 16 (0 : BitVec 128) = writeBytes m a (List.replicate 16 0) := by
  rw [write_eq_writeBytes]
  congr 1

theorem syms_write (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) : (s.write sz r x).syms = s.syms := rfl
theorem syms_setV (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).syms = s.syms := rfl
theorem idxTable_length : idxTable.length = 4 := rfl

/-- The last 16 bytes of a writable text of `N` bytes at `D₀`, for the piece
of it from byte `w` on (`cryptAlT_ok`'s `hbig`). -/
theorem tail_big {rs : List Region} {D₀ D : Addr} {N w n : Nat} (hwr : Covers [⟨D₀, N⟩] rs) (hN : N < 2 ^ 64)
    (hD : D = D₀ + BitVec.ofNat 64 w) (hn : w + n = N) :
    16 ≤ N → n % 16 ≠ 0 → ∃ E, E + BitVec.ofNat 64 (16 - n % 16) = D + BitVec.ofNat 64 (n - n % 16) ∧
      InRegions rs E 16 := fun h16 _ =>
  ⟨D₀ + BitVec.ofNat 64 (N - 16), by
    rw [hD, Offset.add_add, Offset.add_add]; congr 2; omega, in_off hwr (by omega) hN⟩

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `crSeg2T`: `crSeg2`, the keystream block zeroed by one store. -/
theorem crSeg2T_ok {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} (h : CrMid Ctx St W SP k R icb P D n m₀ j s) (hj : n - j < 16) :
    WP isa crSeg2T s (Cr2 Ctx St W SP k R icb P D n m₀ j) := by
  have hn' := h.data.ok.lt
  have hle := h.le
  have he := h.env
  have w₁ := he.perm.stW (show 64 + 16 ≤ 80 by decide)
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x4 = BitVec.ofNat 64 (if n - j = 0 then 0 else 1) ∧
      Others [.x4, .x9] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      (n - j = 0 → s₁.mem = s.mem) ∧
      (n - j ≠ 0 → s₁.mem = s.mem.write (St + BitVec.ofNat 64 64) 16 0))
    (WP.ite (decide (n - j = 0)) (eval_zero h.x24 (by omega_arith)) (fun ht => ?_) (fun hf => ?_))
    fun s₁ ⟨x4₁, g₁, sp₁, rd₁, wr₁, m0₁, m1₁⟩ => ?_)
  · have h0 : n - j = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      exact ⟨by simp [gpr_write, h0], by others_tac, rfl, rfl, rfl, fun _ => rfl, fun h' => absurd h0 h'⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.run ⟨_, by arun [he.x20, w₁, VOp.eval, v_setV_self, gpr_setV, mem_setV, wr_setV, rd_setV, sp_setV], rfl⟩ fun s' hs' => by
      subst hs'
      refine ⟨by simp [gpr_write, h0], by others_tac, rfl, rfl, rfl, fun h' => absurd h' h0, fun _ => ?_⟩
      simp only [mem_write, mem_setV, gpr_write, he.x20]
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x5₂, x3₂, r₂⟩ : ∃ s₂, runBlock isa (ctrArgs ++ [ptr .x3 .x20 64]) s₁ =
      some s₂ ∧ s₂.gpr .x0 = Ctx ∧ s₂.gpr .x1 = BitVec.ofNat 64 R ∧ s₂.gpr .x2 = St + BitVec.ofNat 64 48 ∧
      s₂.gpr .x5 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x3 = St + BitVec.ofNat 64 64 ∧
      Regs [.x0, .x1, .x2, .x5, .x3] s₁ s₂ := by
    refine ⟨_, by rw [ctrArgs_eq]; arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, g₁ .x21 (by decide), he.x21]
    · simp [gpr_write, g₁ .x22 (by decide), h.x22]
    · simp [gpr_write, g₁ .x20 (by decide), he.x20]
    · simp [gpr_write, g₁ .x19 (by decide), he.x19]
    · simp [gpr_write, g₁ .x20 (by decide), he.x20]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have gg : ∀ r, r ∉ [Reg.x4, .x9] ++ [.x0, .x1, .x2, .x5, .x3] → s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (fun h' => hr (List.mem_append_right _ h')), g₁ r (fun h' => hr (List.mem_append_left _ h'))]
  have hsp : s₂.sp = s.sp := by rw [r₂.sp, sp₁]
  have hrd : s₂.rd = s.rd := by rw [r₂.rd, rd₁]
  have hwr : s₂.wr = s.wr := by rw [r₂.wr, wr₁]
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => gg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
  -- The memory: the keystream block zeroed if there are bytes left.
  have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [r₂.mem]
    by_cases h0 : n - j = 0
    · rw [m0₁ h0]; exact Frame.refl _ _
    · rw [m1₁ h0, write_zero16]
      exact writeBytes_frame' _ (by simp)
  have dD : ∀ r ∈ [(⟨St + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.data.ok.st.sub_right (Lay.stSub (by decide))
  have hdD : ∀ (q : Addr) (l : Nat), Region.Sub ⟨q, l⟩ ⟨D, n⟩ → l ≤ n → bytesAt s₂.mem q l = bytesAt s.mem q l :=
    fun q l hs hl => bytesAt_frame fz (fun r hr => (dD r hr).sub_left hs) (by omega_arith)
  refine ⟨he₂, h.kept.of_eq fun r hr => gg r (by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    by rw [gg _ (by decide), h.x22], h.rounds, h.le, hj, by rw [gg _ (by decide), h.x23],
    by rw [gg _ (by decide), h.x24], by rw [gg _ (by decide), h.x25], h.data.of_eq hrd hwr, fun hc₀ => ?_, ?_,
    fun hc₀ => by rw [hdD _ _ (Region.sub_prefix h.le) h.le]; exact h.done hc₀,
    by rw [hdD _ _ (Offset.sub_base D (by omega_arith)) (by omega_arith)]; exact h.rest, h.whole,
    h.frame.trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩), ?_⟩
  · have hcb : blockAt s₂.mem (St + BitVec.ofNat 64 48) = blockAt s.mem (St + BitVec.ofNat 64 48) :=
      blockAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by decide)) (by decide) (by decide)
    by_cases h0 : n - j = 0
    · exact (h.ctr hc₀).congr hcb (by rw [r₂.mem, m0₁ h0])
    · exact Ctr.of_aligned (h.ctr hc₀) (h.whole.resolve_left h0) hcb
  · intro h0
    have e := bytesAt_writeBytes_self s.mem (St + BitVec.ofNat 64 64) (List.replicate 16 (0 : Byte)) (by decide)
    simp only [List.length_replicate] at e
    rw [r₂.mem, m1₁ h0, write_zero16, Spec.Gcm.blockAt, e]
    rfl
  · have hnb : (if n - j = 0 then 0 else 1) ≤ 1 := by split <;> omega_arith
    exact ctrCall_of L he₂ h.rounds x0₂ x1₂ x2₂ x3₂ (by rw [r₂.others _ (by decide), x4₁]) x5₂
      (by have := L.sw; rw [BitVec.toNat_add, toNat_ofNat_of_lt (by decide)]; omega_arith)
      ((L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by omega_arith)))
      (L.st_st (.inl (by decide)) (by decide) (by omega_arith))
      (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)) (he₂.perm.stC (by omega_arith))

omit L in
/-- `ksTail` run: the 16 bytes at `E` (ending the `r` bytes at `x23`) XORed
with the keystream block moved up. -/
theorem ksTail_run {E : Addr} {r : Nat} (hr : r < 16) {s : State} (he : Env Ctx St W SP s)
    (h23 : s.gpr .x23 = E + BitVec.ofNat 64 (16 - r)) (h24 : s.gpr .x24 = BitVec.ofNat 64 r)
    (hE : InRegions s.wr E 16) :
    ∃ s', runBlock isa ksTail s = some s' ∧
      s'.mem = s.mem.write E 16 (s.mem.read E 16 ^^^ VG.Proof.AesGcm.AArch64.Tail.upV (s.mem.read (St + BitVec.ofNat 64 64) 16) r) ∧
      Others [.x9, .x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hks := he.perm.stR (show 64 + 16 ≤ 80 by decide)
  have h16 : (BitVec.setWidth 64 (16#16) <<< 0 : BitVec 64) = BitVec.ofNat 64 16 := by decide
  have hsub : BitVec.ofNat 64 16 - BitVec.ofNat 64 r = BitVec.ofNat 64 (16 - r) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  have hx10 : E + BitVec.ofNat 64 (16 - r) - BitVec.ofNat 64 (16 - r) = E := BitVec.add_sub_cancel _ _
  have hEr := in_left (rd := s.rd) hE
  refine ⟨_, by
    simp only [ksTail, shift, List.cons_append, List.nil_append]
    arun [he.x20, h23, h24, h16, hsub, hx10, hEr, hE, VOp.eval, v_setV, gpr_setV, mem_setV, wr_setV, rd_setV,
      sp_setV, rd_write, hks, syms_write, syms_setV, idxTable_length, Nat.reduceDiv, Nat.zero_div, v_write, BitVec.add_zero]
    , ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [mem_setV, mem_write]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, gpr_setV, hr]

omit L in
/-- `Cr3` depends on no register but those it names. -/
theorem Cr3.keep {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s s' : State} (h : Cr3 Ctx St W SP k R icb P D n m₀ j s)
    (hg : Others [.x9] s s') (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Cr3 Ctx St W SP k R icb P D n m₀ j s' :=
  { env := h.env.keep (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr
    kept := h.kept.of_others hg
    le := h.le, lt16 := h.lt16
    x23 := by rw [hg _ (by decide), h.x23]
    x24 := by rw [hg _ (by decide), h.x24]
    x25 := by rw [hg _ (by decide), h.x25]
    data := h.data.of_eq hrd hwr
    ctr0 := fun h0 hc => by rw [hm]; exact h.ctr0 h0 hc
    ctr1 := fun h0 hc => by rw [hm]; exact h.ctr1 h0 hc
    done := fun hc => by rw [hm]; exact h.done hc
    rest := by rw [hm]; exact h.rest
    whole := h.whole
    frame := by rw [hm]; exact h.frame }

omit L in
/-- `crTailT`: `crTail`, or, for a text of `N` (at least 16) bytes whose last
16 end the piece and may be written, `ksTail`. -/
theorem crTailT_ok {k : Reg → BitVec 64} {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat}
    {m₀ : Mem} {j : Nat} {s : State} {N : Nat} (h : Cr3 Ctx St W SP k R icb P D n m₀ j s)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hbig : 16 ≤ N → n - j ≠ 0 → ∃ E, E + BitVec.ofNat 64 (16 - (n - j)) = D + BitVec.ofNat 64 j ∧
      InRegions s.wr E 16) :
    WP isa crTailT s (CrOut Ctx St W SP k R icb P D n m₀) := by
  have hj := h.lt16
  refine WP.ite (decide (n - j = 0)) (eval_zero h.x24 (by have := h.data.ok.lt; omega)) (fun ht => ?_)
    (fun hf' => ?_)
  · have h0 : n - j = 0 := of_decide_eq_true ht
    refine WP.block_nil (crOut_of_xor h ?_ (fun _ _ => rfl) rfl rfl rfl)
    rw [h0]; exact (writeBytes_nil _ _).symm
  have h0 : n - j ≠ 0 := of_decide_eq_false hf'
  obtain ⟨s₁, run₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x9 .x26 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (N / 16) ∧ Regs [.x9] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp [gpr_write, h26, lsr_ofNat _ _ hN]
  have h₁ := h.keep r₁.others r₁.mem r₁.sp r₁.rd r₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (N / 16 = 0)) (eval_zero x9₁ (by omega)) (fun _ => crTail_ok h₁) (fun hf => ?_)
  have hbN : 16 ≤ N := by have := of_decide_eq_false hf; omega
  obtain ⟨E, hE, hEw⟩ := hbig hbN h0
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := ksTail_run (r := n - j) (by omega) h₁.env
    (by rw [h₁.x23, hE]) h₁.x24 (by rw [r₁.wr]; exact hEw)
  refine WP.of_runBlock ⟨s₂, run₂, crOut_of_xor h₁ ?_ (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂⟩
  rw [m₂, Tail.ks_mem _ _ _ (by omega), hE]

/-- `cryptAlT`: `crypt` from the start of a keystream block, for a text of
`N` bytes (in `x26`) whose last 16 bytes, if it is at least a block long and
the piece ends in a partial block, end the piece and may be written. -/
theorem cryptAlT_ok (v : GcmImpl) {k : Reg → BitVec 64} {R P : Nat} {icb : Block} {D : Addr} {n : Nat}
    {s : State} (h : CrIn Ctx St W SP k R P D n s) (hP : P % 16 = 0) {N : Nat}
    (h26 : k .x26 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hbig : 16 ≤ N → n % 16 ≠ 0 → ∃ E, E + BitVec.ofNat 64 (16 - n % 16) = D + BitVec.ofNat 64 (n - n % 16) ∧
      InRegions s.wr E 16) :
    WP isa (cryptAlT v.callees) s (CrOut Ctx St W SP k R icb P D n s.mem) := by
  have hc : ∀ {m' : Mem}, Frame (crFrame St W D n) s.mem m' → ciphOf m' Ctx R = ciphOf s.mem Ctx R :=
    fun hf => ciph_frame hf (ctx_crFrame L h.data) h.rounds
  have hj : 0 + 16 * ((n - 0) / 16) = n - n % 16 := by omega
  exact WP.seq (WP.mono (WP.with_rdwr (crArgs_ok L (h.mid (icb := icb) hP))) fun s₁ ⟨h₁, _, w₁⟩ =>
    WP.seq (WP.mono (WP.with_rdwr (ctrCall1_ok L v h₁ (hc h₁.frame))) fun s₂ ⟨⟨h₂, hlt⟩, _, w₂⟩ =>
    WP.seq (WP.mono (WP.with_rdwr (crSeg2T_ok L h₂ hlt)) fun s₃ ⟨h₃, _, w₃⟩ =>
    WP.seq (WP.mono (WP.with_rdwr (ctrCall2_ok L v h₃ (hc h₃.frame))) fun s₄ ⟨h₄, _, w₄⟩ =>
      crTailT_ok h₄ ((h₄.kept .x26 (by decide)).trans h26) hN fun hb h0 => by
        obtain ⟨E, hE, hw⟩ := hbig hb (by omega)
        refine ⟨E, ?_, by rw [w₄, w₃, w₂, w₁]; exact hw⟩
        rw [hj, show n - (n - n % 16) = n % 16 by omega, hE]))))

end

end VG.Proof.AesGcm.AArch64

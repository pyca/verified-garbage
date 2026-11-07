module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2Tail
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBufX
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes from `buf`

`Avx2Tail.fromBuf` XORs the keystream left in `buf` with the source into the
destination, at `rsi + r11`: by `XorBuf.xorBufXTo 5`, 32 bytes at a time
while at least 32 remain, or with `vl` by `XorBuf.xorBufTo`, eight bytes at
a time: then all the destination is done (`DoneT`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.ChaCha20.X86_64.Avx2 (TPre edp edq eL ebp edR eqR D0 Q0 KS frT eL_lt in_eqR)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (r9_not_calleeSaved)

/-- All the destination done. -/
structure DoneT (s₀ : State) (s : State) : Prop where
  r9 : s.gpr .r9 = ebp s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  frame : Frame (frT s₀) s₀.mem s.mem

/-- At the end of the last bytes: as `DoneT`, but memory outside the
function's regions is known only at the return address (`vg_chacha20_xor`
uses the stack below it). -/
structure FinT (s₀ : State) (s : State) : Prop where
  r9 : s.gpr .r9 = ebp s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

theorem DoneT.fin {s₀ : State} (hp : TPre s₀) {s : State} (h : DoneT s₀ s) : FinT s₀ s :=
  ⟨h.r9, h.keep, h.rd, h.wr, h.data, h.frame.readW (Region.contains_self _ _) (Avx2.ret_frT hp) (by decide)⟩

/-- The source and the destination of the last `n` bytes, from byte `p`. -/
abbrev winS (s₀ : State) (p n : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 p, n⟩
abbrev winQ (s₀ : State) (p n : Nat) : Region := ⟨edq s₀ + BitVec.ofNat 64 p, n⟩

theorem winS_sub {s₀ : State} {p n : Nat} (h : p + n ≤ eL s₀) : Region.Sub (winS s₀ p n) (edR s₀) :=
  Offset.sub_base _ (by omega_arith)
theorem winQ_sub {s₀ : State} {p n : Nat} (h : p + n ≤ eL s₀) : Region.Sub (winQ s₀ p n) (eqR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem not_winQ {s₀ : State} {p n k : Nat} (h : p + n ≤ eL s₀) (hk : k < eL s₀) (ho : k < p ∨ p + n ≤ k) :
    ¬ (winQ s₀ p n).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := by
  have := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
  split <;> omega_arith

/-- The separation `XorBuf` needs of the last `n` bytes, from byte `p`. -/
theorem sep_of {s₀ : State} (hp : TPre s₀) {p n : Nat} (hn : p + n ≤ eL s₀) (hn256 : n ≤ 256) :
    XorBuf.Sep (edq s₀ + BitVec.ofNat 64 p) (edp s₀ + BitVec.ofNat 64 p) (ebp s₀) n :=
  ⟨(hp.q_b.sub_left (winQ_sub hn)).sub_right (Region.sub_prefix (by omega_arith)), by
    rcases hp.alias with he | hdis
    · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
    · exact .inr ((hdis.sub_left (winS_sub hn)).sub_right (winQ_sub hn)), by omega_arith⟩

theorem toR10_ok (s : State) :
    WP isa (.block [.mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi)]) s fun s' =>
      s'.gpr .r10 = s.gpr .r11 + s.gpr .rsi ∧ (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_setReg_self, gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsi = .r10)]
  · simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags]

theorem toR10X_ok (s : State) :
    WP isa (.block [.mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi), .mov .r11 (.reg .rsi),
      .mov .rsi (.reg .r9)]) s fun s' =>
      s'.gpr .r10 = s.gpr .r11 + s.gpr .rsi ∧ s'.gpr .r11 = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .r9 ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r a b c => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_setReg_self, gpr_setReg_of_ne _ _ (by decide : ¬Reg.r10 = .rsi),
      gpr_setReg_of_ne _ _ (by decide : ¬Reg.r10 = .r11), gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsi = .r10)]
  · simp only [gpr_setReg_self, gpr_setReg_of_ne _ _ (by decide : ¬Reg.r11 = .rsi),
      gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsi = .r10), gpr_arithFlags]
  · simp only [gpr_setReg_self, gpr_setReg_of_ne _ _ (by decide : ¬Reg.r9 = .r11),
      gpr_setReg_of_ne _ _ (by decide : ¬Reg.r9 = .r10), gpr_arithFlags]
  · simp only [gpr_setReg_of_ne _ _ a, gpr_setReg_of_ne _ _ b, gpr_setReg_of_ne _ _ c, gpr_arithFlags]

/-- `fromBuf vl` of the `n` bytes left (`buf` in `r9`), where `buf` holds
bytes `p … p + n` of the keystream, the destination the first `p` bytes
done and the source from byte `p` intact: then all the destination is
done. -/
theorem fromBufY_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p n : Nat} (hn : p + n = eL s₀) (hn256 : n ≤ 256)
    {s : State} (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (h11 : s.gpr .r11 = edq s₀ - edp s₀)
    (hr9 : s.gpr .r9 = ebp s₀) (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hkeep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r)
    (hdone : ∀ k < p, s.mem (edq s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0)
    (hrest : ∀ k < n, s.mem (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) = D0 s₀ (p + k))
    (hks : ∀ k < n, s.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + k) 0)
    (hframe : Frame (frT s₀) s₀.mem s.mem) :
    WP isa (Impl.ChaCha20.X86_64.Avx2Tail.fromBuf vl) s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hD : s.gpr .r11 + s.gpr .rsi = edq s₀ + BitVec.ofNat 64 p := by
    rw [h11, hrsi, XorBuf.sub_add_add]
  have hwD : InRegions s.wr (edq s₀ + BitVec.ofNat 64 p) n :=
    ⟨eqR s₀, by rw [hwr]; exact hp.w_q, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hrS : InRegions (s.rd ++ s.wr) (edp s₀ + BitVec.ofNat 64 p) n :=
    ⟨edR s₀, by rw [hrd, hwr]; exact hp.r_d, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hrB : InRegions (s.rd ++ s.wr) (ebp s₀) n :=
    ⟨Avx2.bufR (ebp s₀), List.mem_append_right _ (by rw [hwr]; exact hp.w_b), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩
  -- What both ways leave, from what `xorBufTo` and `xorBufXTo` do.
  have fin : ∀ s' : State, (∀ k < n, s'.mem (edq s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) =
        s.mem (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) ^^^ s.mem (ebp s₀ + BitVec.ofNat 64 k)) →
      Frame [⟨edq s₀ + BitVec.ofNat 64 p, n⟩] s.mem s'.mem → s'.gpr .r9 = ebp s₀ →
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) → s'.rd = s₀.rd → s'.wr = s₀.wr → DoneT s₀ s' := by
    intro s' hd hf h9 hk hr hw
    refine ⟨h9, hk, hr, hw, fun k hk' => ?_, hframe.trans (hf.sub fun r hr => ?_)⟩
    · by_cases hkp : k < p
      · rw [hf _ (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          exact not_winQ (by omega_arith) hk' (.inl hkp))]
        exact hdone k hkp
      · rw [show edq s₀ + BitVec.ofNat 64 k = edq s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) by
          rw [Offset.add_add, Nat.add_sub_cancel' (by omega_arith)], hd _ (by omega_arith),
          hrest _ (by omega_arith), hks _ (by omega_arith), Nat.add_sub_cancel' (by omega_arith)]
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨eqR s₀, by simp, winQ_sub (by omega_arith)⟩
  cases vl
  · -- `xorBufXTo 5 r10 r11`, from `r11` (the source) to `r10`, with `buf` in `rsi`.
    show WP isa (.seq (.block [.mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi), .mov .r11 (.reg .rsi),
      .mov .rsi (.reg .r9)]) (Impl.ChaCha20.X86_64.XorBuf.xorBufXTo 5 .r10 .r11)) s _
    refine WP.seq (WP.mono (toR10X_ok s) fun s₁ ⟨r10₁, r11₁, rsi₁, g, m₁, rd₁, wr₁⟩ => ?_)
    refine WP.mono (ChaCha20.X86_64.XorBufX.xorBufXTo_ok (w := 5) (by decide) (d := .r10) (sr := .r11)
      (by decide) (by decide) (D := edq s₀ + BitVec.ofNat 64 p) (S := edp s₀ + BitVec.ofNat 64 p)
      (B := ebp s₀) (n := n) (by rw [r10₁]; exact hD) (by rw [r11₁, hrsi]) (by rw [rsi₁, hr9])
      (by rw [g _ (by decide) (by decide) (by decide), hrdx])
      (sep_of hp (by omega_arith) hn256) (by rw [wr₁]; exact hwD) (by rw [rd₁, wr₁]; exact hrS)
      (by rw [rd₁, wr₁]; exact hrB))
      fun s' hq => fin s' (fun k hk => by rw [hq.data k hk, m₁]) (by rw [← m₁]; exact hq.frame) ?_ (fun r hr => ?_)
        (by rw [hq.rd, rd₁, hrd]) (by rw [hq.wr, wr₁, hwr])
    · rw [hq.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        g _ (by decide) (by decide) (by decide), hr9]
    · obtain ⟨_, a, b, c⟩ := r9_not_calleeSaved hr
      have e : r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hq.keep r a b c e.1 e.2.1 e.2.2.1 e.2.2.2.2, g r e.2.2.2.1 e.2.2.2.2 e.2.1]; exact hkeep r hr
  · -- `xorBufTo r10 rsi r9`.
    show WP isa (.seq (.block [.mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi)])
      (Impl.ChaCha20.X86_64.XorBuf.xorBufTo .r10 .rsi .r9)) s _
    refine WP.seq (WP.mono (toR10_ok s) fun s₁ ⟨r10₁, g, m₁, rd₁, wr₁⟩ => ?_)
    refine WP.mono (XorBuf.xorBufTo_ok (d := .r10) (sr := .rsi) (b := .r9) (by decide) (by decide) (by decide)
      (D := edq s₀ + BitVec.ofNat 64 p) (S := edp s₀ + BitVec.ofNat 64 p) (B := ebp s₀) (n := n)
      (by rw [r10₁]; exact hD) (by rw [g _ (by decide), hrsi]) (by rw [g _ (by decide), hr9])
      (by rw [g _ (by decide), hrdx]) (sep_of hp (by omega_arith) hn256) (by rw [wr₁]; exact hwD)
      (by rw [rd₁, wr₁]; exact hrS) (by rw [rd₁, wr₁]; exact hrB))
      fun s' hq => fin s' (fun k hk => by rw [hq.data k hk, m₁]) (by rw [← m₁]; exact hq.frame) ?_ (fun r hr => ?_)
        (by rw [hq.rd, rd₁, hrd]) (by rw [hq.wr, wr₁, hwr])
    · rw [hq.keep _ (by decide) (by decide) (by decide), g _ (by decide), hr9]
    · obtain ⟨_, a, b, c⟩ := r9_not_calleeSaved hr
      have e : r ≠ .r10 := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hq.keep r a b c, g r e]; exact hkeep r hr

end VG.Proof.ChaCha20.X86_64.Avx2Tail

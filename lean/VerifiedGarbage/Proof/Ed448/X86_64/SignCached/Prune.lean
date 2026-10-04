import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.X86_64.Words57
import VerifiedGarbage.Proof.Ed448.Prune

/-!
# Ed448 signing with a cached public key on x86-64: `s`

The first 57 bytes of the hash in the frame, loaded into registers
(`loads_ok`), pruned (`mods_ok`) and stored at `s` (`stores_ok`): the number
of the 57 bytes at `s` is `Spec.Ed448.prune` of the hash (`prune_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk fH)
open VG.Proof.Ed448.X86_64.Verify (Within add_add ea_stk ne_cs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Ed448 (prune_nat)
open VG.Proof.Ed448.X86_64 (decode57 byte_of_zero take57)

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Word `k` of the hash. -/
abbrev hw (t : State) (L : Lay) (k : Nat) : BitVec 64 := t.mem.readW (L.SP + BitVec.ofNat 64 (16 + 8 * k)) 64

/-- The registers the pruning writes. -/
abbrev pRegs : List Reg := [.r8, .r9, .r10, .r11, .rax, .rcx, .rsi, .rdi]

theorem pRegs_cs : ∀ r ∈ calleeSaved, r ∉ pRegs := by decide
theorem mRegs_cs : ∀ r ∈ calleeSaved, r ∉ [Reg.r8, .rsi, .rdi] := by decide

theorem loads_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block loads) t fun t' => (t'.mem = t.mem ∧ t'.mxcsr = t.mxcsr ∧
      t'.gpr .r8 = hw t L 0 ∧ t'.gpr .r9 = hw t L 1 ∧ t'.gpr .r10 = hw t L 2 ∧ t'.gpr .r11 = hw t L 3 ∧
      t'.gpr .rax = hw t L 4 ∧ t'.gpr .rcx = hw t L 5 ∧ t'.gpr .rsi = hw t L 6) ∧ Keep pRegs t t' := by
  have s0 := hc.inFr (d := 16) (by omega)
  have s1 := hc.inFr (d := 24) (by omega)
  have s2 := hc.inFr (d := 32) (by omega)
  have s3 := hc.inFr (d := 40) (by omega)
  have s4 := hc.inFr (d := 48) (by omega)
  have s5 := hc.inFr (d := 56) (by omega)
  have s6 := hc.inFr (d := 64) (by omega)
  refine WP.keep _ ?_ (by decide)
  xrun [loads, fH, ea_stk, hc.rsp, Nat.reduceAdd, s0, s1, s2, s3, s4, s5, s6, RegUpd.mxcsr_setReg]

theorem mods_ok (t : State) :
    WP isa (.block mods) t fun t' => (t'.mem = t.mem ∧ t'.mxcsr = t.mxcsr ∧
      t'.gpr .r8 = (t.gpr .r8 &&& BitVec.ofNat 64 (2 ^ 64 - 4)) ∧
      t'.gpr .rsi = (t.gpr .rsi ||| BitVec.ofNat 64 (2 ^ 63)) ∧ t'.gpr .rdi = 0) ∧
      Keep [.r8, .rsi, .rdi] t t' := by
  refine WP.keep _ ?_ (by decide)
  xrun [mods, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
  exact congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-4)) = BitVec.ofNat 64 (2 ^ 64 - 4))

/-- `s` lies in the data of the frame. -/
theorem w_s : WOk L ⟨L.S, 64⟩ :=
  .inr (.inr (.inr ⟨64, show L.SP + BitVec.ofNat 64 320 = L.SP + BitVec.ofNat 64 256 + BitVec.ofNat 64 64 from
    (add_add L.SP 256 64).symm, show 64 + 64 ≤ 192 by decide⟩))

theorem st_ok {t : State} (hc : Ctx L g mx m₀ t) {k : Nat} (hk : k < 8) (r : Reg) :
    WP isa (.block [Instr.store (stk (fS + 8 * k)) r]) t fun t' =>
      t'.mem = t.mem.writeW (L.SP + BitVec.ofNat 64 (320 + 8 * k)) (t.gpr r) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inFrW (d := 320 + 8 * k) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp, fS, w,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The first `n` stores of `stores`. -/
abbrev storesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (fS + 8 * k)) (sRegs.getD k .r8)

theorem stores_ok (hL : L.Ok) : ∀ n ≤ 8, ∀ t : State, Ctx L g mx m₀ t →
    WP isa (.block (storesN n)) t fun t' => Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      Frame [⟨L.S, 64⟩] t.mem t'.mem ∧
      ∀ j < n, t'.mem.readW (L.SP + BitVec.ofNat 64 (320 + 8 * j)) 64 = t.gpr (sRegs.getD j .r8)
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc => by
    rw [storesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (stores_ok hL n (by omega) t hc) fun u ⟨hu, ug, uf, uw⟩ => ?_
    refine WP.mono (st_ok hu (k := n) (by omega) _) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨L.S, 64⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        rw [Lay.S]; exact Offset.contains _ (by omega) (by omega) (by omega))
    have hc' : Ctx L g mx m₀ v := hu.of_frame hL vrd vwr (fun r _ => by rw [vg]) (by rw [vmx])
      (hf1.mono fun r hr => List.mem_append_left _ hr) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact w_s
    refine ⟨hc', by rw [vg, ug], uf.trans hf1, fun j hj => ?_⟩
    rw [vm]
    by_cases hjn : j = n
    · subst hjn; rw [Mem.readW_writeW_self64, ug]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uw j (by omega)]

theorem prune_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block prune) t fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.S, 64⟩] t.mem t'.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem L.S 57) =
        Spec.Ed448.prune (Spec.Sha3.bytesAt t.mem L.H 114) := by
  rw [prune, WP.block_append_iff]
  refine WP.mono (loads_ok hc) fun u ⟨⟨hmu, hxu, u8, u9, u10, u11, uax, ucx, usi⟩, ku⟩ => ?_
  have hu : Ctx L g mx m₀ u := hc.regs ku.2.1 ku.2.2 hmu hxu fun r hr => ku.gpr (pRegs_cs r hr)
  rw [WP.block_append_iff]
  refine WP.mono (mods_ok u) fun v ⟨⟨hmv, hxv, v8, vsi, vdi⟩, kv⟩ => ?_
  have hv : Ctx L g mx m₀ v := hu.regs kv.2.1 kv.2.2 hmv hxv fun r hr => kv.gpr (mRegs_cs r hr)
  have v9 : v.gpr .r9 = u.gpr .r9 := kv.gpr (by decide)
  have v10 : v.gpr .r10 = u.gpr .r10 := kv.gpr (by decide)
  have v11 : v.gpr .r11 = u.gpr .r11 := kv.gpr (by decide)
  have vax : v.gpr .rax = u.gpr .rax := kv.gpr (by decide)
  have vcx : v.gpr .rcx = u.gpr .rcx := kv.gpr (by decide)
  refine WP.mono (stores_ok hL 8 (by omega) v hv) fun w ⟨hw', _, hfw, ww⟩ => ⟨hw', by rw [← hmu, ← hmv]; exact hfw, ?_⟩
  have f0 : w.mem.readW (L.SP + BitVec.ofNat 64 320) 64 = v.gpr .r8 := ww 0 (by omega)
  have f1 : w.mem.readW (L.SP + BitVec.ofNat 64 328) 64 = v.gpr .r9 := ww 1 (by omega)
  have f2 : w.mem.readW (L.SP + BitVec.ofNat 64 336) 64 = v.gpr .r10 := ww 2 (by omega)
  have f3 : w.mem.readW (L.SP + BitVec.ofNat 64 344) 64 = v.gpr .r11 := ww 3 (by omega)
  have f4 : w.mem.readW (L.SP + BitVec.ofNat 64 352) 64 = v.gpr .rax := ww 4 (by omega)
  have f5 : w.mem.readW (L.SP + BitVec.ofNat 64 360) 64 = v.gpr .rcx := ww 5 (by omega)
  have f6 : w.mem.readW (L.SP + BitVec.ofNat 64 368) 64 = v.gpr .rsi := ww 6 (by omega)
  have f7 : w.mem.readW (L.SP + BitVec.ofNat 64 376) 64 = v.gpr .rdi := ww 7 (by omega)
  rw [decode57]
  simp only [Lay.S, Lay.SP, add_add, Nat.reduceAdd] at f0 f1 f2 f3 f4 f5 f6 f7 ⊢
  rw [f0, f1, f2, f3, f4, f5, f6, byte_of_zero _ _ (f7.trans vdi), v8, v9, v10, v11, vax, vcx, vsi, u8, u9,
    u10, u11, uax, ucx, usi, Spec.Ed448.prune, take57, decode57]
  simp only [hw, Lay.SP, add_add, Nat.reduceMul, Nat.reduceAdd]
  refine Eq.trans ?_ (prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm
  have c₁ : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  have c₂ : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, c₁, c₂]

end

end VG.Proof.Ed448.X86_64.SignCached

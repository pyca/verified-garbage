import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

variable {G : Spec.Mgf1.Hash}

theorem arg_read {s u : State} (hp : Pre G s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 7) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem arg_keep {s : State} {m : Mem} (hp : Pre G s) (hf : Frame (vwrR s) s.mem m) {j : Nat} (hj : j < 7) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.argsStack
    · exact hp.argsScr

theorem load_pre {s t : State} (hp : Pre G s) (hsp : t.gpr .rsp = fb s) (hrd : t.rd = s.rd)
    (hf : Frame (vwrR s) s.mem t.mem) :
    WP isa (.block [.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧
        u.gpr .rdx = stackArg s 5 ∧ u.gpr .rcx = stackArg s 6 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [arg, ea_sp, hsp, arg_read hp hrd (show 5 < 7 by decide), arg_read hp hrd (show 6 < 7 by decide),
    arg_keep hp hf (show 5 < 7 by decide), arg_keep hp hf (show 6 < 7 by decide)]

theorem args_ok {s u : State} (hp : Pre G s) (L : Lay u (fb s) (stackArg s 3))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 3) V W)
    (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem)
    (h17 : W 17 = s.gpr .rsi) (h18 : W 18 = s.gpr .rdi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h38 : W 38 = s.gpr .r9) :
    WP isa (.block Impl.RsaPss.X86_64.Precomputed.pubArgs) u fun u' =>
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧ Lay u' (fb s) (stackArg s 3) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 3) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧ (∀ i < nW, 4 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = off (stackArg s 3) oEm ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 5 ∧
      u'.gpr .rcx = stackArg s 6 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx := by
  refine WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] ?_ (by decide) |>
    WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  unfold Impl.RsaPss.X86_64.Precomputed.pubArgs
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (pubArgs_ok L R h17 h18 h19 h20 h22 h38)) fun t ⟨⟨k, L1, ⟨W1, R1, ha, hb⟩, hdi, hsi, _, _, h8, h9⟩, f⟩ => ?_
  have hf := vframe_keep hp.toVPre hw L.rsp hM f
  refine WP.mono (load_pre hp L1.rsp (k.2.1.trans hrd) hf) fun v ⟨k2, hm, hdx, hcx⟩ => ?_
  refine ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm]), ⟨W1, hm ▸ R1, ha, hb⟩,
    (k2.gpr (by decide)).trans hdi, (k2.gpr (by decide)).trans hsi, hdx, hcx,
    (k2.gpr (by decide)).trans h8, (k2.gpr (by decide)).trans h9⟩

end VG.Proof.RsaPss.X86_64.Pc

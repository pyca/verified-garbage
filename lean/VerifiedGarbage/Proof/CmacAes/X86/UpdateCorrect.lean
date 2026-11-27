module

public import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
public import VerifiedGarbage.Proof.Aes.X86.Chain
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CMAC on x86: `vg_cmac_aes_update` is correct

The chaining by calls (`updateCalls`), for any implementation of
`vg_aes_ctr32_to`, and the chaining around any chain (`updateChain`), which
shares its prologue and epilogue and their invariant (`LInv`): between them
the memory changes only within the chain's bytes of the scratch buffer, and
the chaining value is in a register (`Chain.mid_wp`), until it is stored in
the state.
-/

@[expose] public section

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (eval_e)

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2080) :
    m.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by omega_using [h₂])
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

theorem UPre.ret_stk {s₀ : State} (_hp : UPre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 32) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

/-- The return address, which nothing writes. -/
theorem ret_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  (UPre.big_of hf).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact hp.ret_stk) (by decide)

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ (N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (UPre.big_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega_using [hsc]) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact ret_read hp h.frame
  · show Spec.Aes.bytesAt s₂.mem ((St s₀).setWidth 64) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [r₂.mem, u₁.mem, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body v.callee) .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok v hp (by omega_using [hn]) h

theorem updateCalls_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa (updateCalls v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp v hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

/-! ## Around a chain -/

open VG.Proof.Aes.X86.AesNi (st st_ext getD_st getD_ofFn byte_xor)
open VG.Proof.Aes.X86.Chain (ChainOk Env pxor cmac_ok st_readW st_getD of_ok)

/-- `pxor` of two registers is §4.2's `⊕` of their bytes. -/
theorem st_pxor (a d : BitVec 128) :
    (Vector.ofFn fun i : Fin 16 => (Spec.Cmac.xor (st a).toList (st d).toList).getD i 0) = st (pxor a d) := by
  apply st_ext
  intro i hi
  rw [getD_ofFn hi, Proof.Cmac.getD_xor (by simp) (by simpa using hi), st_getD a hi, st_getD d hi, getD_st _ hi]
  exact (byte_xor a d i).symm

theorem env_of {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ 0 s) :
    Env (W s₀) (R s₀) (St s₀) (Dp s₀) (N s₀) (S s₀) s := by
  have big := UPre.big_of h.frame
  have ha : ∀ i, argAddr s i = argAddr s₀ i := fun i => by simp only [argAddr, h.esp]
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have arg' : ∀ {i : Nat}, i < 6 → arg s i = arg s₀ i := fun hi => by
    show s.mem.readW (argAddr s _) 32 = _
    rw [ha]; exact hp.arg_keep big hi
  exact {
    a0 := arg' (by decide), a1 := (arg' (by decide)).trans (arg_ofNat s₀ 1)
    a2 := arg' (by decide), a3 := arg' (by decide), a4 := (arg' (by decide)).trans (arg_ofNat s₀ 4)
    a5 := arg' (by decide)
    argIn := fun i hi => by rw [hrw, ha]; exact hp.arg_in hi
    argScr := fun i hi => by rw [ha]; exact hp.args_scr.sub_left (hp.arg_sub hi)
    rounds := hp.rounds, schFit := hp.sch_fit, sch := by rw [hrw, hp.rd]; simp
    schScr := hp.sch_scr, scrFit := hp.scr_fit, scr := by rw [h.wr, hp.wr]; simp
    iv := by rw [h.wr, hp.wr]; simp
    ivScr := hp.st_scr, datFit := hp.data_fit, dat := by rw [hrw, hp.rd]; simp
    datScr := hp.data_scr }

theorem chainMid_wp {c : Impl.Aes.X86.Chain} (hc : ChainOk c) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv s₀ 0 s₁) (hn : 0 < N s₀) :
    WP isa (c.mid Impl.Aes.X86.Chain.cmac) s₁ (LInv s₀ (N s₀)) := by
  have hle := hc.le
  have hs : Proof.Aes.X86.Chain.sched (W s₀) (R s₀) s₁.mem = Proof.Aes.X86.Chain.sched (W s₀) (R s₀) s₀.mem :=
    UPre.sched_bytes hp (UPre.big_of h.frame)
  have wsub : Region.Sub ⟨(S s₀).setWidth 64, c.written⟩ ⟨(S s₀).setWidth 64, 2064⟩ :=
    Region.sub_prefix (by omega_using [hle])
  refine WP.mono (Proof.Aes.X86.Chain.mid_wp (w := none) hc cmac_ok (env_of hp h) (fun hw => nomatch hw) hn (I := fun k x m =>
    Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m ∧
      (st x).toList = Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16) ((blks s₀).take k))
    ⟨h.frame, by rw [st_readW]; exact h.state⟩ (fun hI hf => ⟨hI.1.trans (hf.sub fun r hr => ?_), hI.2⟩)
    (fun hk hI hE => ⟨hI.1, ?_⟩)) fun t ⟨x, m', hI, hf, hm', esi, esp, rd, wr⟩ =>
      ⟨esi, esp.trans h.esp, rd.trans h.rd, wr.trans h.wr, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, wsub⟩
  · rename_i k x e m
    rw [hs] at hE
    rw [take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single, ← hI.2,
      ← UPre.block_bytes hp (UPre.big_of hI.1) hk, ← st_readW, hE]
    exact congrArg (fun x => (Spec.Aes.cipher (R s₀) _ x).toList) (st_pxor _ _).symm
  · rw [hm']
    exact hI.1.writeW (r := stR s₀) List.mem_cons_self _ (Region.contains_self _ _)
  · rw [hm', ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact hI.2

theorem updateChain_wp {c : Impl.Aes.X86.Chain} (hc : ChainOk c) {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa (updateChain c) s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ => WP.seq (WP.mono ?_ fun _ h₂ => epilogue_wp hp h₂))
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h₁
  · exact WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ =>
      chainMid_wp hc hp h₁ (by omega_using [hn])

theorem update_cases (c : Impl.Aes.X86.Ctr32) :
    (∃ k, Impl.Aes.X86.Chain.of c.name = some k ∧ update c = updateChain k) ∨ update c = updateCalls c :=
  Proof.Aes.X86.Chain.choose_cases _ _ _

/-- `vg_cmac_aes_update` over `v`, whichever chaining it is. -/
theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  rcases update_cases v.callee with ⟨c, h, e⟩ | e <;> rw [e]
  · exact updateChain_wp (of_ok h) h0
  · exact updateCalls_wp v h0

end VG.Proof.CmacAes.X86

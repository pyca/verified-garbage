module

public import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
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
`vg_aes_ctr32_to`, and the chaining with AES-NI (`updateNi`), which shares
its prologue and epilogue and their invariant (`LInv`): between them the
memory stays as the prologue left it, and the chaining value after `k`
blocks is in `xmm0` (`XInv`), until it is stored in the state.
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

/-! ## With AES-NI -/

open VG.X86.RegUpd
open VG.Proof.Aes.X86.AesNi (st st_ext st_toList getD_st getD_ofFn byte_xor byte_roundKey ofInt_natCast Keys
  aes_ok)

/-- The 16 bytes a register was loaded from. -/
theorem st_readW (m : Mem) (a : Addr) : (st (m.readW a 128)).toList = Spec.Aes.bytesAt m a 16 := by
  rw [st_toList]
  exact List.map_congr_left fun i hi => VG.Proof.Gcm.X86.byte_readW m a (List.mem_range.mp hi)

theorem st_getD (a : BitVec 128) {i : Nat} (hi : i < 16) : (st a).toList.getD i 0 = byte a i := by
  rw [st_toList, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- `pxor` of two registers is §4.2's `⊕` of their bytes. -/
theorem st_pxor (a d : BitVec 128) :
    (Vector.ofFn fun i : Fin 16 => (Spec.Cmac.xor (st a).toList (st d).toList).getD i 0) =
      st (XBinOp.eval .pxor a d) := by
  apply st_ext
  intro i hi
  rw [getD_ofFn hi, Proof.Cmac.getD_xor (by simp) (by simpa using hi), st_getD a hi, st_getD d hi, getD_st _ hi]
  exact (byte_xor a d i).symm

/-- The invariant of the loop after `k` blocks: the memory is `m`, as the
prologue left it, and the chaining value is in `xmm0`. -/
structure XInv (s₀ : State) (m : Mem) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - k)
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)
  edx : s.gpr .edx = St s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m
  chain : (st (s.xmm .xmm0)).toList =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16) ((blks s₀).take k)

theorem niPre_eq : niPre = .mov .edi (argOp 4) :: .mov .eax (argOp 0) :: .mov .ecx (argOp 1) ::
    .mov .edx (argOp 2) :: ([.movdquLoad .xmm0 (at_ .edx 0)] : List Instr) := rfl

/-- `niPre`, from a state whose stack arguments are the entry state's. -/
theorem niPre_run {s₀ s : State} {Q : State → Prop} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : ∀ i < 6, InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4)
    (harg : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (hst : InRegions (s.rd ++ s.wr) ((arg s₀ 2).setWidth 64) 16)
    (k : ∀ s', s'.gpr .edi = arg s₀ 4 → s'.gpr .eax = arg s₀ 0 → s'.gpr .ecx = arg s₀ 1 →
      s'.gpr .edx = arg s₀ 2 → s'.gpr .esi = s.gpr .esi → s'.gpr .esp = s.gpr .esp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.xmm .xmm0 = s.mem.readW ((arg s₀ 2).setWidth 64) 128 → Q s') :
    WP isa (.block niPre) s Q := by
  rw [niPre_eq]
  refine wp_arg (s₀ := s₀) hesp (hin 4 (by decide)) (harg 4 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr]; exact hin 0 (by decide))
    (by rw [u₁.mem]; exact harg 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 1 (by decide))
    (by rw [u₂.mem, u₁.mem]; exact harg 1 (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 2 (by decide))
    (by rw [u₃.mem, u₂.mem, u₁.mem]; exact harg 2 (by decide)) fun s₄ u₄ => ?_
  obtain mem₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain ea : s₄.ea (at_ .edx 0) = (arg s₀ 2).setWidth 64 := by
    rw [ea_at', u₄.gpr]
    show (arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64 = _
    rw [add0']
  obtain hin₄ : InRegions (s₄.rd ++ s₄.wr) ((arg s₀ 2).setWidth 64) 16 := by
    rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hst
  rw [WP.block_cons_iff]
  refine ⟨s₄.setXmm .xmm0 (s₄.mem.readW ((arg s₀ 2).setWidth 64) 128), by
    simp only [isa, reduceExec, State.load128, ea, hin₄, ite_true, Option.map_some],
    WP.block_nil (k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)⟩
  · rw [gpr_setXmm, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [gpr_setXmm, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [gpr_setXmm, u₄.other _ (by decide), u₃.gpr]
  · rw [gpr_setXmm, u₄.gpr]
  · rw [gpr_setXmm, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [gpr_setXmm, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [mem_setXmm, mem₄]
  · rw [rd_setXmm, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [wr_setXmm, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [xmm_setXmm_self, mem₄]

theorem niPre_wp {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ 0 s) :
    WP isa (.block niPre) s (XInv s₀ s.mem 0) := by
  obtain big := UPre.big_of h.frame
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  refine niPre_run h.esp (fun i hi => by rw [hrw]; exact hp.arg_in hi) (fun i hi => hp.arg_keep big hi)
    (by rw [hrw]; exact ⟨stR s₀, by simp [hp.wr], Region.contains_self _ _⟩)
    fun s' edi eax ecx edx esi esp mem rd wr x => ⟨by rw [esi, h.esi], ?_, eax, ?_, edx, by rw [esp, h.esp],
      by rw [rd, h.rd], by rw [wr, h.wr], mem, ?_⟩
  · rw [edi, Nat.sub_zero]; exact arg_ofNat s₀ 4
  · rw [ecx]; exact arg_ofNat s₀ 1
  · rw [x, st_readW]; exact h.state

/-- The round keys, read from the schedule that `eax` points at. -/
theorem niKeys {s : State} {P : BitVec 32} {nr : Nat} (hnr : nr ≤ 14) (hfit : P.toNat + 240 ≤ 2 ^ 32)
    (heax : s.gpr .eax = P) (hmem : (⟨P.setWidth 64, 240⟩ : Region) ∈ s.rd ++ s.wr) :
    Keys nr (Spec.Aes.bytesAt s.mem (P.setWidth 64) (16 * (nr + 1))) s := by
  obtain he : ∀ j ≤ nr, s.ea (Impl.Aes.X86.AesNi.at_ .eax (16 * j)) =
      P.setWidth 64 + BitVec.ofNat 64 (16 * j) := fun j hj => by
    show addr (s.gpr .eax) (16 * j) = _
    rw [heax]
    exact addr_eq (by omega_using [hfit, hj, hnr])
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj]
    exact ⟨_, hmem, Offset.contains_base _ (by omega_using [hj, hnr]) (by omega_using [hj, hnr])⟩
  · rw [he j hj]
    have h := byte_roundKey s.mem (P.setWidth 64) (L := 16 * (nr + 1)) (j := j) (by omega_using [hj])
    rw [ofInt_natCast] at h
    exact h

theorem sub_one_ofNat {n : Nat} (h : 0 < n) : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega_using [h]⟩
  rw [BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

/-- The block at `esi` (at `D`) XORed into `xmm0`, which is then enciphered. -/
theorem niBlock_wp {s : State} {D : Addr} {nr : Nat} {w : List Byte} {rest : Prog isa} {Q : State → Prop}
    (hea : s.ea (at_ .esi 0) = D) (hin : InRegions (s.rd ++ s.wr) D 16) (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hK : Keys nr w s) (hc : s.gpr .ecx = BitVec.ofNat 32 nr)
    (k : ∀ s', st (s'.xmm .xmm0) =
        Spec.Aes.cipher nr w (st (XBinOp.eval .pxor (s.xmm .xmm0) (s.mem.readW D 128))) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa rest s' Q) :
    WP isa (.seq (.block [.movdquLoad .xmm7 (at_ .esi 0), .xop (.bin .pxor .xmm0 .xmm7)])
      (.seq (Impl.Aes.X86.AesNi.aes [.xmm0]) rest)) s Q := by
  obtain ⟨d, hd⟩ : ∃ d, s.mem.readW D 128 = d := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, (s.setXmm .xmm7 d).setXmm .xmm0
    (XBinOp.eval .pxor ((s.setXmm .xmm7 d).xmm .xmm0) ((s.setXmm .xmm7 d).xmm .xmm7)) = s₁ := ⟨_, rfl⟩
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm7 d, by
    simp only [isa, reduceExec, State.load128, hea, hin, ite_true, Option.map_some, hd], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₁, hs₁ ▸ rfl, WP.block_nil ?_⟩
  obtain x₁ : s₁.xmm .xmm0 = XBinOp.eval .pxor (s.xmm .xmm0) d := by
    rw [← hs₁, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_self]
  obtain g₁ : s₁.gpr = s.gpr := by rw [← hs₁, gpr_setXmm, gpr_setXmm]
  obtain m₁ : s₁.mem = s.mem := by rw [← hs₁, mem_setXmm, mem_setXmm]
  obtain rd₁ : s₁.rd = s.rd := by rw [← hs₁, rd_setXmm, rd_setXmm]
  obtain wr₁ : s₁.wr = s.wr := by rw [← hs₁, wr_setXmm, wr_setXmm]
  obtain hK₁ : Keys nr w s₁ :=
    ⟨hK.le, by simp only [State.ea, g₁, rd₁, wr₁]; exact hK.keys, by simp only [State.ea, g₁, m₁]; exact hK.bytes⟩
  refine WP.seq (WP.mono (aes_ok [.xmm0] (by decide) (by decide) hnr s₁ hK₁ (by rw [g₁, hc])) fun s₂ ⟨c₂, f₂⟩ => ?_)
  exact k s₂ (by rw [c₂ .xmm0 List.mem_cons_self, x₁, hd]) (f₂.gpr.trans g₁) (f₂.mem.trans m₁) (f₂.rd.trans rd₁)
    (f₂.wr.trans wr₁)

/-- One block. -/
theorem niBody_wp {s₀ : State} (hp : UPre s₀) {m : Mem} (hm : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀)
    {s : State} (h : XInv s₀ m k s) :
    WP isa niBody s fun s' => XInv s₀ m (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  obtain ea : s.ea (at_ .esi 0) = (Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k) := by
    rw [ea_at', h.esi]
    show (Dp s₀ + BitVec.ofNat 32 (16 * k) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [add0']
    exact hp.dataA hk
  obtain hin : InRegions (s.rd ++ s.wr) ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
    rw [h.rd]
    exact ⟨dataR s₀, by simp [hp.rd], Offset.contains_base _ (by omega_using [hk]) (by have := hp.data_fit; omega_using [this, hk])⟩
  obtain hK := niKeys (s := s) (nr := R s₀) (by rcases hp.rounds with h | h | h <;> omega_using [h]) hp.sch_fit h.eax
    (by rw [h.rd]; simp [hp.rd])
  rw [h.mem, UPre.sched_bytes hp hm] at hK
  refine niBlock_wp ea hin hp.rounds hK h.ecx fun s₂ c₂ g₂ m₂ rd₂ wr₂ => ?_
  obtain hpos : 0 < N s₀ - k := by omega_using [hk]
  obtain edi' : s.gpr .edi - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [h.edi, sub_one_ofNat hpos]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, readSrc, isa, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, xmm_setReg, xmm_arithFlags, zf_setReg, zf_arithFlags, reduceCtorEq, ↓reduceIte, g₂]
  · rw [h.esi, BitVec.add_assoc]
    exact congrArg (Dp s₀ + ·) (BitVec.ofNat_add ..).symm
  · exact edi'
  · exact h.eax
  · exact h.ecx
  · exact h.edx
  · exact h.esp
  · rw [rd₂, h.rd]
  · rw [wr₂, h.wr]
  · rw [m₂, h.mem]
  · rw [c₂, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single, ← h.chain,
      ← UPre.block_bytes hp hm hk, ← h.mem, ← st_readW]
    exact congrArg (fun x => (Spec.Aes.cipher (R s₀) _ x).toList) (st_pxor _ _).symm
  · rw [edi', MdStream.X86.ofNat_beq_zero (by have : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt; omega_using [this])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

theorem niLoop_wp {s₀ : State} (hp : UPre s₀) {m : Mem} (hm : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀)
    {s : State} (h : XInv s₀ m k s) : WP isa (.loop niBody .ne) s (XInv s₀ m (N s₀)) := by
  refine WP.loop (M := isa) (body := niBody) (c := .ne) (Q := XInv s₀ m (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ XInv s₀ m j t) ?_ (N s₀ - k) s ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (niBody_wp hp hm hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [MdStream.X86.eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h'⟩

/-- The chaining value stored: the invariant the epilogue starts from. -/
theorem niPost_wp {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hm : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {s : State}
    (h : XInv s₀ m (N s₀) s) : WP isa (.block niPost) s (LInv s₀ (N s₀)) := by
  obtain ea : s.ea (at_ .edx 0) = (St s₀).setWidth 64 := by
    rw [ea_at', h.edx]
    show (St s₀ + BitVec.ofNat 32 0).setWidth 64 = _
    rw [add0']
  obtain hout : InRegions s.wr ((St s₀).setWidth 64) 16 := by
    rw [h.wr]
    exact ⟨stR s₀, by simp [hp.wr], Region.contains_self _ _⟩
  rw [niPost, WP.block_cons_iff]
  refine ⟨{ s with mem := s.mem.writeW ((St s₀).setWidth 64) (s.xmm .xmm0) }, by
    simp only [isa, reduceExec, State.store128, ea, hout, ite_true], WP.block_nil ⟨h.esi, h.esp, h.rd, h.wr, ?_, ?_⟩⟩
  · show Frame _ (savedMem s₀) (s.mem.writeW _ _)
    rw [h.mem]
    exact hm.writeW (r := stR s₀) List.mem_cons_self _ (Region.contains_self _ _)
  · show Spec.Aes.bytesAt (s.mem.writeW _ _) _ 16 = _
    rw [← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide), h.chain]

theorem niMid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.seq (.block niPre) (.seq (.loop niBody .ne) (.block niPost)))) s₁
      (LInv s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (niPre_wp hp h) fun s₂ x₂ => ?_)
    exact WP.seq (WP.mono (niLoop_wp hp (UPre.big_of h.frame) (by omega_using [hn]) x₂) fun _ x₃ =>
      niPost_wp hp h.frame x₃)

theorem updateNi_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa updateNi s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (niMid_wp hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

/-- `vg_cmac_aes_update` over `v`, whichever chaining it is. -/
theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  unfold update
  split
  · exact updateNi_wp h0
  · exact updateCalls_wp v h0

end VG.Proof.CmacAes.X86

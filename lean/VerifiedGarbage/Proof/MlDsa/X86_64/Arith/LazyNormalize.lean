import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyReduce
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNttLayers

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok ifp ifn GOnly
  add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (toY rcxLoop)
open VG.Spec.MlDsa (q n coeffAt)

def Normalized (m : Mem) (fP : Addr) (G : Poly) (i : Nat) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = if k < 8 * i then (residue G[k]!).val else G[k]!.val

abbrev reduceBody : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ toY reduceLazy ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .alu .add .rdx (.imm 32)] ++ [.alu .sub .rcx (.imm 1)]

theorem normalize_step {fP : Addr} {G : Poly} {i : Nat} (hi : i < 32) {s : State} (hc : YConsts s)
    (hb : ∀ k < 256, G[k]!.val < 17 * q)
    (hdx : s.gpr .rdx = coeffAddr fP (8 * i)) (hS : Normalized s.mem fP G i) (hw : pR fP ∈ s.wr) :
    WP isa (.block reduceBody) s fun s' =>
      Normalized s'.mem fP G (i + 1) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right _ hw) j0
  rw [reduceBody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (by decide +kernel)
    (P := fun l t => Arith.DLanes (t.xmm .xmm0) (fun e => residue G[8 * i + 4 * l + e]!))
    fun l hl => reduce_ok (yonly_yconsts o1 hc (by decide) (by decide) (by decide) l hl).toVConsts
      (fun e he => by
        rw [State.proj_xmm, L1 l hl, hdx, add_ofNat_zero, dword_readW _ _ he, lane_load,
          coeffAddr_add, ← coeffAt_eq, hS _ (by omega), ifn (by omega)])
      (fun e he => hb _ (by omega))) fun s2 ⟨V2, o2⟩ => ?_
  have o12 := o1.trans o2
  have hv : ∀ l < 2, ∀ e < 4, (dword (s2.lane .xmm0 l) e).toNat = (residue G[8 * i + 4 * l + e]!).val :=
    fun l hl e he => V2 l hl e he
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have g2 : s2.gpr .rdx = coeffAddr fP (8 * i) := by rw [o12.gpr, hdx]
  rw [g2, o12.mem]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      split
      · have := hv 0 (by decide) (k - 8 * i) (by omega)
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this; exact this
      · have := hv 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this; exact this
    · rename_i h
      rw [hS k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show 8 * i + 8 = 8 * (i + 1) by omega]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP j0)
  · exact ylanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12 hc
      (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o12.wr]
  · rw [o12.gpr]
  · rw [o12.gpr]
  · exact o12.mxcsr


theorem normalize_ok {fP : Addr} {G : Poly} {f : VG.Spec.MlDsa.Poly}
    (hr : Rel 17 G f) (s : State) (hc : YConsts s) (hdi : s.gpr .rdi = fP)
    (hS : PolyIs s.mem fP G) (hwf : pR fP ∈ s.wr) :
    WP isa normalizeLazy s fun s' => VG.Spec.MlDsa.PolyIs s'.mem fP f ∧ BInvY fP s s' := by
  refine WP.seq ?_
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by vrund [hdi]; exact ⟨by gonlyd, rfl⟩) fun w ⟨hdx, og, hy⟩ => ?_
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide)
    (fun i u => Normalized u.mem fP G i ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ YConsts u ∧
      Keep [.rcx, .rdx] w u ∧ Frame [pR fP] w.mem u.mem ∧ u.mxcsr = w.mxcsr)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, og.mem, ifn (by omega)]; exact polyIs_toNat hS hk,
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      ylanes_gpr (s := w) (o.lane hu) (YOnly.refl [] w) cw (by decide) (by decide),
      o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun i hi u ⟨hS', hdx', hc', hk', hf', hx'⟩ => WP.mono (normalize_step hi hc'
        (fun k hk => (hr k hk).1) hdx' hS' (by rw [hk'.2.2, og.keep.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', (hk'.trans hk'').mono (by simp), hf'.trans hf'', hx''.trans hx'⟩, hcx, hzf⟩))
    fun u ⟨hS', _, hc', hk', hf', hx'⟩ => ?_
  refine ⟨VG.Proof.MlDsa.Arith.polyIs_of_toNat fun k hk => ?_,
    ⟨(og.keep.trans hk').mono (by simp), by rw [← og.mem]; exact hf', hc', hx'.trans og.mxcsr⟩⟩
  rw [hS' k hk, ifp (by omega), (hr k hk).2]

end VG.Proof.MlDsa.X86_64.Arith.Lazy

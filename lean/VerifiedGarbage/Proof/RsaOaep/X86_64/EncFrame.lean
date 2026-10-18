module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sel
public import VerifiedGarbage.Spec.RsaOaep.AnyHash
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP encryption on x86-64: the precondition by name, and the frame

`EPre` names the facts of `encK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (H : Spec.Mgf1.Hash) {G : Spec.Mgf1.Hash}

/-- The selectors, `hash` and `mgf1_hash`, and the tables, `hash_fns` and
`mgf1_fns`. -/
abbrev selH (s : State) : Nat := (stackArg s 10).toNat
abbrev selG (s : State) : Nat := (stackArg s 11).toNat
abbrev tabH (s : State) : Addr := stackArg s 12
abbrev tabG (s : State) : Addr := stackArg s 13

/-- The caller's read-only buffers, the stack arguments and the tables. -/
def rdL (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩,
    ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, H.len⟩, ⟨stackArgAddr s 0, 112⟩, ⟨tabH s, 24⟩,
    ⟨tabG s, 24⟩]

/-- The table of the hash function `i` names: its streaming functions, as
`Fns` says of them, and the hash function they compute. -/
theorem fns_of_tab {stack : Nat} {e : State} {i : Nat} {p : Addr} (h : TabFns stack e i p) :
    ∃ T Hh, Spec.HashFns.streaming i = some T ∧ Spec.HashId.mgf1 i = some Hh ∧ HashFns.StreamingOK T Hh ∧
      Fns stack e T (e.mem.readW (off p (8 * 0)) 64) (e.mem.readW (off p (8 * 1)) 64)
        (e.mem.readW (off p (8 * 2)) 64) := by
  unfold TabFns Spec.HashFns.tableOf at h
  split at h
  · rename_i T hT
    obtain ⟨Hh, eH, ok⟩ := HashFns.streaming_ok hT
    obtain ⟨h0, h1, h2⟩ := h
    have e0 : off p (8 * 0) = p := BitVec.add_zero p
    refine ⟨T, Hh, hT, eH, ok, ⟨?_, h1, h2⟩⟩
    rw [e0]; exact h0
  · exact h.elim

/-- `encK.pre`, by name. -/
structure EPre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  hrd : Covers (rdL H s) s.rd
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩]
  d_out_n : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  d_out_e : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  d_out_lb : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  d_out_ms : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  d_out_sd : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, H.len⟩
  d_out_scr : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_out_args : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  d_n_scr : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_e_scr : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_lb_scr : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_ms_scr : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_sd_scr : (⟨stackArg s 4, H.len⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_scr_args : (⟨stackArg s 6, (stackArg s 7).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  d_ret_out : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  d_ret_n : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  d_ret_e : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  d_ret_lb : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  d_ret_ms : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  d_ret_sd : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, H.len⟩
  d_ret_scr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_ret_args : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  d_stk_out : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  d_stk_n : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  d_stk_e : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  d_stk_lb : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  d_stk_ms : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  d_stk_sd : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 4, H.len⟩
  d_stk_scr : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_stk_args : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wL : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wM : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wSd : (stackArg s 4).toNat + H.len ≤ 2 ^ 64
  wS : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hsl : 8 * (((s.gpr .rcx).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 7).toNat
  d_out_tH : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨tabH s, 24⟩
  d_out_tG : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨tabG s, 24⟩
  d_tH_scr : (⟨tabH s, 24⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_tG_scr : (⟨tabG s, 24⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  d_stk_tH : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨tabH s, 24⟩
  d_stk_tG : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨tabG s, 24⟩
  wTH : (tabH s).toNat + 24 ≤ 2 ^ 64
  wTG : (tabG s).toNat + 24 ≤ 2 ^ 64
  fH : TabFns encStack s (selH s) (tabH s)
  fG : TabFns encStack s (selG s) (tabG s)

/-- A read-only buffer of the caller is readable. -/
theorem EPre.rd_in {H : Spec.Mgf1.Hash} {s t : State} (hp : EPre H s) (hrd : t.rd = s.rd) {r : Region} (hr : r ∈ rdL H s) {a : Addr}
    {n : Nat} (hc : r.Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [hrd]; exact hp.hrd.left _ _ ⟨r, hr, hc⟩

/-- A read-only buffer of the caller is in the regions of the entry. -/
theorem EPre.rdIn {H : Spec.Mgf1.Hash} {s : State} (hp : EPre H s) {r : Region} (hr : r ∈ rdL H s) :
    ∀ x, r.Contains x 1 → InRegions (s.rd ++ s.wr ++ abi.reserved encStack s) x 1 :=
  fun x hx => (Covers.left (Covers.left hp.hrd)) x 1 ⟨r, hr, hx⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩

theorem sub_sub' (p : Addr) (a b : Nat) : p - BitVec.ofNat 64 a - BitVec.ofNat 64 b = p - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 16) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

variable {H}

theorem fb_toNat {s : State} (hp : EPre H s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold encStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem EPre.geo {s : State} (hp : EPre H s) : Geo (fb s) (stackArg s 6) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 6, oRsa⟩ ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by unfold frameBytes at *; omega, by unfold oRsa; omega,
    ((hp.d_stk_scr.sub_left (frame_sub s)).sub_right sS), ((hp.d_stk_scr.sub_left (ret_sub s)).sub_right sS)⟩

/-- The address of stack argument `j`, from the frame. -/
theorem argAddr (s : State) (j : Nat) : off (fb s) (frameBytes + 8 + 8 * j) = stackArgAddr s j := by
  simp only [off, fb, stackArgAddr]
  rw [show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem allocState_gpr' (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

/-- The frame's region. -/
abbrev frR (s : State) : Region := ⟨fb s, frameBytes⟩

theorem stackArgAddr_j (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_read {s : State} (hp : EPre H s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 14) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 112⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.d_stk_args.sub_left (frame_sub s)).symm

/-- One stack argument copied to a slot. -/
theorem copy1_ok {s : State} (hp : EPre H s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 14) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [hrd]
    refine hp.hrd.left _ _ ⟨⟨stackArgAddr s 0, 112⟩, by simp [rdL], ?_⟩
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem frame_w {s : State} (hp : EPre H s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))

/-- The slots `encPrologue` stores to, and what. -/
def encPW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    21 (s.gpr .rdi)) 22 (s.gpr .rdx)) 23 (s.gpr .rcx)) 24 (s.gpr .r8)) 25 (s.gpr .r9))
    27 (stackArg s 0)) 28 (stackArg s 1)) 29 (stackArg s 2)) 30 (stackArg s 3)) 31 (stackArg s 4))
    14 (stackArg s 6)) 26 (stackArg s 7)

/-- The words of the table at `p`. -/
def tw (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (8 * i)) 64

/-- The words of tables whose words (`tableWords`) agree. -/
theorem tw_eq {m₁ m₂ : Mem} {p₁ p₂ : Addr}
    (h : Spec.HashFns.tableWords m₁ p₁ = Spec.HashFns.tableWords m₂ p₂) {i : Nat} (hi : i < 3) :
    tw m₁ p₁ i = tw m₂ p₂ i := by
  simp only [Spec.HashFns.tableWords, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  have e0 : ∀ (m : Mem) (p : Addr), tw m p 0 = m.readW p 64 := fun m p => by
    simp only [tw, off, Nat.mul_zero]; rw [BitVec.add_zero]
  have e1 : ∀ (m : Mem) (p : Addr), tw m p 1 = m.readW (p + 8) 64 := fun _ _ => rfl
  have e2 : ∀ (m : Mem) (p : Addr), tw m p 2 = m.readW (p + 16) 64 := fun _ _ => rfl
  match i, hi with
  | 0, _ => rw [e0, e0]; exact BitVec.eq_of_toNat_eq h0
  | 1, _ => rw [e1, e1]; exact BitVec.eq_of_toNat_eq h1
  | 2, _ => rw [e2, e2]; exact BitVec.eq_of_toNat_eq h2

/-- The slots after `encPrologue` and `selPrologue`, and what. -/
def encW (s : State) : Nat → BitVec 64 :=
  fnW (selW (encPW s) (selH s) (selG s) (lenOf (selH s)) (lenOf (selG s)))
    (tw s.mem (tabH s) 0) (tw s.mem (tabH s) 1) (tw s.mem (tabH s) 2)
    (tw s.mem (tabG s) 0) (tw s.mem (tabG s) 1) (tw s.mem (tabG s) 2)

theorem encPrologue_eq : encPrologue =
    ([.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8,
      .store (sp sEl) .r9] : List Instr) ++ argSlot 0 sLab ++ argSlot 1 sLabLen ++ argSlot 2 sMsg ++
    argSlot 3 sMsgLen ++ argSlot 4 sSeed ++ argSlot 6 sScr ++ argSlot 7 sScrLen := rfl

/-- The prologue: the slots as `encW` says, the working space untouched. -/
theorem encPro_ok {s : State} (hp : EPre H s) :
    WP isa (.block encPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 6) ∧ Rep t.mem (fb s) (stackArg s 6) (fun o => s.mem (off (stackArg s 6) o)) (encPW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hfr : frR s ∈ (allocState frameBytes s).wr := List.mem_cons_self ..
  have hsc : Scr (allocState frameBytes s) (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have R0 : Rep s.mem (fb s) (stackArg s 6) (fun o => s.mem (off (stackArg s 6) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [encPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have R1 := ((((R0.wf G' (k := 21) (by decide) (s.gpr .rdi)).wf G' (k := 22) (by decide) (s.gpr .rdx)).wf G'
    (k := 23) (by decide) (s.gpr .rcx)).wf G' (k := 24) (by decide) (s.gpr .r8)).wf G' (k := 25) (by decide)
    (s.gpr .r9)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((s.mem.writeW (off (fb s) (8 * 21)) (s.gpr .rdi)).writeW
      (off (fb s) (8 * 22)) (s.gpr .rdx)).writeW (off (fb s) (8 * 23)) (s.gpr .rcx)).writeW (off (fb s) (8 * 24))
      (s.gpr .r8)).writeW (off (fb s) (8 * 25)) (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sOut) (by decide), hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide),
      hsc.st (d := sE) (by decide), hsc.st (d := sEl) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (Frame.refl _ _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  have hfr1 : frR s ∈ t1.wr := k1.2.2 ▸ hfr
  refine WP.mono (copy1_ok hp sp1 hfr1 k1.2.1 f1 (j := 0) (d := sLab) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ hfr1) (k2.2.1.trans k1.2.1) f2
    (j := 1) (d := sLabLen) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ hfr1) (k23.2.1.trans k1.2.1) f3
    (j := 2) (d := sMsg) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ hfr1) (k24.2.1.trans k1.2.1) f4
    (j := 3) (d := sMsgLen) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ hfr1) (k25.2.1.trans k1.2.1) f5
    (j := 4) (d := sSeed) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k26 := k25.trans k6
  refine WP.mono (copy1_ok hp ((k26.gpr (by decide)).trans sp1) (k26.2.2 ▸ hfr1) (k26.2.1.trans k1.2.1) f6
    (j := 6) (d := sScr) (by decide) (by decide)) fun t7 ⟨k7, hm7, f7⟩ => ?_
  have k27 := k26.trans k7
  refine WP.mono (copy1_ok hp ((k27.gpr (by decide)).trans sp1) (k27.2.2 ▸ hfr1) (k27.2.1.trans k1.2.1) f7
    (j := 7) (d := sScrLen) (by decide) (by decide)) fun t8 ⟨k8, hm8, f8⟩ => ?_
  have k18 : Keep [.rax] (allocState frameBytes s) t8 := (k1.trans (k27.trans k8)).mono (by decide)
  have R8 : Rep t8.mem (fb s) (stackArg s 6) (fun o => s.mem (off (stackArg s 6) o)) (encPW s) := by
    rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((((R1.wf G' (k := 27) (by decide) (stackArg s 0)).wf G' (k := 28) (by decide) (stackArg s 1)).wf G'
      (k := 29) (by decide) (stackArg s 2)).wf G' (k := 30) (by decide) (stackArg s 3)).wf G' (k := 31)
      (by decide) (stackArg s 4)).wf G' (k := 14) (by decide) (stackArg s 6)).wf G' (k := 26) (by decide)
      (stackArg s 7)
  have := hp.sp1
  refine ⟨k18, ⟨(k18.gpr (by decide)).trans hsp, k18.2.2 ▸ hfr, ?_, ?_, ?_, ?_, G'.dFS, G'.dRS⟩, R8, f8⟩
  · unfold encStack at this; unfold frameBytes at *; omega
  · unfold frameBytes at *; omega
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 6, 0, (stackArg s 7).toNat * 8, by rw [k18.2.2]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 14 from rfl]
    exact (R8.fr 14 (by decide)).trans (by simp [encPW, upd])

/-- A stack argument is readable. -/
theorem EPre.arg_in {s u : State} (hp : EPre H s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 14) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [hrd]
  refine hp.hrd.left _ _ ⟨⟨stackArgAddr s 0, 112⟩, by simp [rdL], ?_⟩
  rw [argAddr, stackArgAddr_j s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A number of `Spec.RsaOaep.hashIds` and its length, of `lens`. -/
theorem mem_lens {i : Nat} (h : i ∈ Spec.RsaOaep.hashIds) : (i, lenOf i) ∈ lens := by
  simp only [Spec.RsaOaep.hashIds, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A table, through the stack argument `j` (12 or 13), from the frame. -/
theorem EPre.tab {s u : State} (hp : EPre H s) (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j : Nat}
    (hj : j = 12 ∨ j = 13) :
    TabAt u (fb s) j (stackArg s j) (tw s.mem (stackArg s j) 0) (tw s.mem (stackArg s j) 1)
      (tw s.mem (stackArg s j) 2) := by
  have hT : Region.Disjoint (frR s) ⟨stackArg s j, 24⟩ := by
    rcases hj with rfl | rfl
    · exact hp.d_stk_tH.sub_left (frame_sub s)
    · exact hp.d_stk_tG.sub_left (frame_sub s)
  have hw : (stackArg s j).toNat + 24 ≤ 2 ^ 64 := by rcases hj with rfl | rfl <;> [exact hp.wTH; exact hp.wTG]
  have hin : ∀ k < 3, InRegions (u.rd ++ u.wr) (off (stackArg s j) (8 * k)) 8 := fun k hk => by
    rw [hrd]
    refine hp.hrd.left _ _ ⟨⟨stackArg s j, 24⟩, by rcases hj with rfl | rfl <;> simp [rdL], ?_⟩
    exact Offset.contains_base _ (by omega) (by omega)
  have hrdw : ∀ k < 3, ∀ m', Frame [frR s] s.mem m' →
      m'.readW (off (stackArg s j) (8 * k)) 64 = tw s.mem (stackArg s j) k := fun k hk m' hm =>
    hm.readW (r := ⟨stackArg s j, 24⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hT.symm) (by decide)
  refine ⟨hp.arg_in hrd (by omega), fun m' hm => arg_read hp (hf.trans hm) (by omega), ?_, hin 1 (by decide),
    hin 2 (by decide), fun m' hm => ⟨?_, hrdw 1 (by decide) m' (hf.trans hm), hrdw 2 (by decide) m' (hf.trans hm)⟩⟩
  · have := hin 0 (by decide); simpa [off] using this
  · have := hrdw 0 (by decide) m' (hf.trans hm); simpa [off] using this

/-- The prologues: the slots as `encW` says, for the hash functions
the selectors name, the working space untouched. -/
theorem encSel_ok {s : State} (hp : EPre H s) (iH : selH s ∈ Spec.RsaOaep.hashIds)
    (iG : selG s ∈ Spec.RsaOaep.hashIds) :
    WP isa (.block encPrologue) (allocState frameBytes s) fun t => WP isa (selPrologue 10 11) t fun t' =>
      Keep [.rax, .r10] (allocState frameBytes s) t' ∧ Lay t' (fb s) (stackArg s 6) ∧
      Rep t'.mem (fb s) (stackArg s 6) (fun o => s.mem (off (stackArg s 6) o)) (encW s) ∧
      Frame [frR s] s.mem t'.mem := by
  refine WP.mono (encPro_ok hp) fun t ⟨k1, L1, R1, f1⟩ => ?_
  have hrd : t.rd = s.rd := k1.2.1
  refine WP.mono (selPro_ok (mem_lens iH) (mem_lens iG) L1 R1 (hp.arg_in hrd (by decide))
    (hp.arg_in hrd (by decide)) (fun m' hm => ⟨?_, ?_⟩) (hp.tab hrd f1 (.inl rfl)) (hp.tab hrd f1 (.inr rfl)))
    fun t' ⟨L2, k2, R2, f2⟩ => ⟨(k1.trans k2).mono (by decide), L2, R2, f1.trans f2⟩
  · rw [arg_read hp (f1.trans hm) (j := 10) (by decide)]; simp
  · rw [arg_read hp (f1.trans hm) (j := 11) (by decide)]; simp

end VG.Proof.RsaOaep.X86_64

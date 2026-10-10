import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
import VerifiedGarbage.Proof.Framework.X86_64.CallSp

/-!
# AES-GCM streaming encryption out of place, x86-64: the call of the whole blocks

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_encrypt_blocks_to` on `q ≥ 1` whole blocks, with `dst`, `q` and
the working space pushed for it (`blkCall_ok`): what it needs, from the
layout of `s` (`blkPre`), and what it leaves.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

theorem sub_add_ofNat (p : Addr) {b d : Nat} (h : d ≤ b) :
    p - BitVec.ofNat 64 b + BitVec.ofNat 64 d = p - BitVec.ofNat 64 (b - d) := by
  rw [Offset.sub_ofNat_eq p (show b - d ≤ b by omega), Nat.sub_sub_self h]

/-- A prefix of a region covered is covered. -/
theorem covers_prefix {b : Addr} {k L : Nat} {ts : List Region} (h : (⟨b, L⟩ : Region) ∈ ts) (hk : k ≤ L) :
    Covers [⟨b, k⟩] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx
  exact ⟨_, h, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- A part of a region covered is covered. -/
theorem covers_off {p : Addr} {k d m : Nat} {ts : List Region} (h : (⟨p, k⟩ : Region) ∈ ts) (hd : d + m ≤ k)
    (hd' : d < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, m⟩] ts := by
  intro a j ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, h, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := Nat.mod_le ((a - (p + BitVec.ofNat 64 d)).toNat + d) (2 ^ 64)
  omega

/-- A part of a buffer that does not wrap around does not either. -/
theorem off_bound {p : Addr} {o n L : Nat} (hw : p.toNat + L ≤ 2 ^ 64) (h : o + n ≤ L) :
    (p + BitVec.ofNat 64 o).toNat + n ≤ 2 ^ 64 := by
  by_cases hn : n = 0
  · subst hn; have := (p + BitVec.ofNat 64 o).isLt; omega
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem covers_cons' {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil' {ts : List Region} : Covers [] ts := by
  intro a n ⟨x, hx, _⟩; cases hx

section
variable (s : State)

/-- The counter block and `Y` of the state. -/
abbrev ctrR : Region := ⟨St s + BitVec.ofNat 64 48, 16⟩
abbrev yR : Region := ⟨St s + BitVec.ofNat 64 16, 16⟩

/-- What the call reads and writes, on `q` whole blocks after the `o`
bytes done. -/
abbrev blkRd (M : CtxMode) (o q : Nat) : List Region :=
  [kR M s, ⟨Src s + BitVec.ofNat 64 o, q * 16⟩, ⟨SP s - BitVec.ofNat 64 24, 24⟩]
abbrev blkWr (o q : Nat) : List Region := [ctrR s, yR s, ⟨Dst s + BitVec.ofNat 64 o, q * 16⟩, scR s]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem ctr_sub : (ctrR s).Sub (stR s) := Offset.sub_base _ (by decide)
omit hp in
theorem y_sub : (yR s).Sub (stR s) := Offset.sub_base _ (by decide)

omit hp in
theorem pre_sub {o q : Nat} (hq : o + 16 * q ≤ L s) : Region.Sub ⟨Src s + BitVec.ofNat 64 o, q * 16⟩ (srcR s) :=
  Offset.sub_base _ (by omega)
omit hp in
theorem dst_sub {o q : Nat} (hq : o + 16 * q ≤ L s) : Region.Sub ⟨Dst s + BitVec.ofNat 64 o, q * 16⟩ (dR s) :=
  Offset.sub_base _ (by omega)

omit hp in
/-- A region of the stack below `SP - a`, in the stack the code uses. -/
theorem stk_sub {a n : Nat} (ha : a ≤ 2624) (hn : n ≤ a) :
    Region.Sub ⟨SP s - BitVec.ofNat 64 a, n⟩ (tR s) := Offset.sub_below _ (by omega) (by omega)

/-- What the call of `vg_aes_gcm_encrypt_blocks_to` needs. -/
theorem blkPre {o q : Nat} (hq : o + 16 * q ≤ L s) {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 32) (hrd : u.rd = blkRd s M o q) (hwr : u.wr = blkWr s o q)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = St s + BitVec.ofNat 64 48)
    (h_cx : u.gpr .rcx = St s + BitVec.ofNat 64 16) (h_8 : u.gpr .r8 = Src s + BitVec.ofNat 64 o) (h_9 : u.gpr .r9 = BitVec.ofNat 64 q)
    (a0 : stackArg u 0 = Dst s + BitVec.ofNat 64 o) (a1 : stackArg u 1 = BitVec.ofNat 64 q) (a2 : stackArg u 2 = W s + BitVec.ofNat 64 80)
    (hok : M.ok u.mem (K s)) :
    (Proof.AesGcm.encryptBlocksToX86_64M M).pre u := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have hqn : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have wt := hp.w_t
  have wsp := hp.w_sp
  have pr := pre_sub (s := s) hq
  have ds := dst_sub (s := s) hq
  have wst := hp.w_st
  have hargs : (Proof.AesGcm.args u 3) = ⟨SP s - BitVec.ofNat 64 24, 24⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  have hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 32, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  have hstk : (Proof.AesGcm.stk24 u) = ⟨SP s - BitVec.ofNat 64 56, 24⟩ := by
    simp only [Proof.AesGcm.stk24, below, hrsp]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  have tA : Region.Sub ⟨SP s - BitVec.ofNat 64 24, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 32, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tS : Region.Sub ⟨SP s - BitVec.ofNat 64 56, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have ws : (W s + BitVec.ofNat 64 80).toNat = (W s).toNat + 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 80) (by decide)]
    have := hp.w_w; omega
  have st48 : (St s + BitVec.ofNat 64 48).toNat = (St s).toNat + 48 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide)]; omega
  have st16 : (St s + BitVec.ofNat 64 16).toNat = (St s).toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide)]; omega
  have hsp32 : (SP s - BitVec.ofNat 64 32).toNat = (SP s).toNat - 32 := toNat_sub_ofNat (by omega)
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPreM, Proof.AesGcm.arg, hargs, hret,
    hstk, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0, a1, a2, hqn, hrsp, Proof.AesGcm.rounds]
  refine ⟨trivial, trivial, trivial, hp.k_st.sub_right ctr_sub, hp.k_st.sub_right y_sub, hp.k_d.sub_right ds,
    hp.k_w.sub_right scR_sub,
    Offset.disjoint _ (.inr (by decide)) (by omega) (by omega), (hp.st_r.sub_left ctr_sub).sub_right pr,
    (hp.st_d.sub_left ctr_sub).sub_right ds, (hp.st_w.sub_left ctr_sub).sub_right scR_sub,
    (hp.b_st.symm.sub_left ctr_sub).sub_right tA,
    (hp.st_r.sub_left y_sub).sub_right pr, (hp.st_d.sub_left y_sub).sub_right ds,
    (hp.st_w.sub_left y_sub).sub_right scR_sub, (hp.b_st.symm.sub_left y_sub).sub_right tA,
    (hp.r_d.sub_left pr).sub_right ds, (hp.r_w.sub_left pr).sub_right scR_sub,
    (hp.d_w.sub_left ds).sub_right scR_sub, (hp.b_d.symm.sub_left ds).sub_right tA,
    (hp.b_w.symm.sub_left scR_sub).sub_right tA,
    (hp.b_st.sub_left tR').sub_right ctr_sub, (hp.b_st.sub_left tR').sub_right y_sub,
    (hp.b_d.sub_left tR').sub_right ds, (hp.b_w.sub_left tR').sub_right scR_sub,
    hp.b_k.sub_left tS, (hp.b_st.sub_left tS).sub_right ctr_sub, (hp.b_st.sub_left tS).sub_right y_sub,
    (hp.b_r.sub_left tS).sub_right pr, (hp.b_d.sub_left tS).sub_right ds, (hp.b_w.sub_left tS).sub_right scR_sub,
    hp.w_k, by rw [st48]; omega, by rw [st16]; omega, off_bound hp.w_r (by omega), off_bound hp.w_d (by omega),
    by rw [ws]; have := hp.w_w; omega, by rw [hsp32]; omega, by rw [hsp32]; omega, hp.rounds, hok⟩

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
/-- A frame of a region of the stack below `SP - a` is one of the stack the
code uses. -/
theorem frame_stk {m m' : Mem} {a n : Nat} (ha : a ≤ 2624) (hn : n ≤ a)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 a, n⟩] m m') : Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨tR s, by simp, stk_sub (s := s) ha hn⟩

/-- What the call of `vg_aes_gcm_encrypt_blocks_to` needs, after the push. -/
theorem blkEntry {o q : Nat} (hq : o + 16 * q ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = St s + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = Src s + BitVec.ofNat 64 o) (h_9 : st.gpr .r9 = BitVec.ofNat 64 q)
    (h_10 : st.gpr .r10 = Dst s + BitVec.ofNat 64 o) (h_ax : st.gpr .rax = W s + BitVec.ofNat 64 80) :
    (Proof.AesGcm.encryptBlocksToX86_64M M).pre ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) ∧
      Covers (blkRd s M o q ++ blkWr s o q) ((pushed [.rax, .r9, .r10] st).rd ++ (pushed [.rax, .r9, .r10] st).wr) ∧
      Covers (blkWr s o q) (pushed [.rax, .r9, .r10] st).wr ∧
      stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) 0 =
        Dst s + BitVec.ofNat 64 o ∧
      stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) 1 = BitVec.ofNat 64 q ∧
      stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) 2 =
        W s + BitVec.ofNat 64 80 := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  have hn8 : 8 * [Reg.rax, .r9, .r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r9, .r10] (by decide) hn8
  have hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r9, .r10][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r9, .r10] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r9, .r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r9, .r10] st).mem
      (pushed [.rax, .r9, .r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r9, .r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  -- The memory the call starts from, from `s`'s.
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  have fS : Frame (wR s ++ [tR s]) st.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega)
  have ea : ∀ i, i < 3 → stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) i =
      (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * i)) 64 :=
    fun i hi => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega)
  have a0 := ea 0 (by decide)
  have a1 := ea 1 (by decide)
  have a2 := ea 2 (by decide)
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have hok : M.ok ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_disj hp) hp.w_k hp.ok
  have hpre := blkPre hp hq hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_cx) (by rw [gU _ (by decide)]; exact h_8)
    (by rw [gU _ (by decide)]; exact h_9) (by rw [a0, h_10]) (by rw [a1, h_9]) (by rw [a2, h_ax]) hok
  have hPw : (pushed [.rax, .r9, .r10] st).wr = ⟨SP s - BitVec.ofNat 64 24, 24⟩ :: wR s := by
    rw [pushed_wr, hsp, hwr, hp.wr]; rfl
  have hPr : (pushed [.rax, .r9, .r10] st).rd = [kR M s, srcR s, aR s] := by rw [pushed_rd, hrd, hp.rd]
  have cC : ∀ {ts : List Region}, stR s ∈ ts → Covers [ctrR s] ts := fun h =>
    covers_off (k := 80) (d := 48) (m := 16) h (by decide) (by decide)
  have cY : ∀ {ts : List Region}, stR s ∈ ts → Covers [yR s] ts := fun h =>
    covers_off (k := 80) (d := 16) (m := 16) h (by decide) (by decide)
  have cSc : ∀ {ts : List Region}, wkR s ∈ ts → Covers [scR s] ts := fun h =>
    covers_off (k := 2192) (d := 80) (m := 2112) h (by decide) (by decide)
  have cD : ∀ {ts : List Region}, dR s ∈ ts → Covers [⟨Dst s + BitVec.ofNat 64 o, q * 16⟩] ts := fun h =>
    covers_off (k := L s) h (by omega) (by omega)
  have cR : ∀ {ts : List Region}, srcR s ∈ ts → Covers [⟨Src s + BitVec.ofNat 64 o, q * 16⟩] ts := fun h =>
    covers_off (k := L s) h (by omega) (by omega)
  have cw : Covers (blkWr s o q) (pushed [.rax, .r9, .r10] st).wr := by
    rw [hPw]
    exact covers_cons' (cC (by simp)) (covers_cons' (cY (by simp)) (covers_cons' (cD (by simp))
      (covers_cons' (cSc (by simp)) covers_nil')))
  have cr : Covers (blkRd s M o q ++ blkWr s o q) ((pushed [.rax, .r9, .r10] st).rd ++ (pushed [.rax, .r9, .r10] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (cR (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (cC (by simp)) (covers_cons' (cY (by simp))
      (covers_cons' (cD (by simp)) (covers_cons' (cSc (by simp)) covers_nil'))))))
  exact ⟨hpre, cr, cw, by rw [a0, h_10], by rw [a1, h_9], by rw [a2, h_ax]⟩

/-- The call of `vg_aes_gcm_encrypt_blocks_to` on `q` whole blocks, with
`dst`, `q` and the working space pushed for it. -/
theorem blkCall_ok (T : BlkToFn M) {o q : Nat} (hq : o + 16 * q ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = St s + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = Src s + BitVec.ofNat 64 o) (h_9 : st.gpr .r9 = BitVec.ofNat 64 q)
    (h_10 : st.gpr .r10 = Dst s + BitVec.ofNat 64 o) (h_ax : st.gpr .rax = W s + BitVec.ofNat 64 80) :
    WP isa (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (blkWr s o q ++ [tR s]) st.mem st'.mem ∧
      blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q =
        ctr32 (ciph s) (blockAt st.mem (St s + BitVec.ofNat 64 48)) (blocksAt st.mem (Src s + BitVec.ofNat 64 o) q) ∧
      blockAt st'.mem (St s + BitVec.ofNat 64 48) = Nat.repeat inc32 q (blockAt st.mem (St s + BitVec.ofNat 64 48)) ∧
      blockAt st'.mem (St s + BitVec.ofNat 64 16) =
        ghashFrom (hk s) (blockAt st.mem (St s + BitVec.ofNat 64 16)) (blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  have hn8 : 8 * [Reg.rax, .r9, .r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r9, .r10] (by decide) hn8
  have hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r9, .r10][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r9, .r10] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r9, .r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r9, .r10] st).mem
      (pushed [.rax, .r9, .r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r9, .r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  -- The memory the call starts from, from `s`'s.
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  have fS : Frame (wR s ++ [tR s]) st.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega)
  have ea : ∀ i, i < 3 → stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) i =
      (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * i)) 64 :=
    fun i hi => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega)
  have a0 := ea 0 (by decide)
  have a1 := ea 1 (by decide)
  have a2 := ea 2 (by decide)
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain ⟨hpre, cr, cw, -, -, -⟩ := blkEntry hp hq hsp hrd hwr hf h_di h_si h_dx h_cx h_8 h_9 h_10 h_ax
  -- What the push and the return address leave as it was.
  have keep : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint (tR s) → n ≤ 2 ^ 64 →
      bytesAt (pushed [.rax, .r9, .r10] st).callEntry.mem p n = bytesAt st.mem p n := fun hd hn => by
    rw [bytesAt_frame hE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))) hn,
      bytesAt_frame hpf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))) hn]
  have keepB : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint (tR s) →
      blockAt (pushed [.rax, .r9, .r10] st).callEntry.mem p = blockAt st.mem p := fun hd => by
    rw [blockAt, blockAt, keep hd (by decide)]
  have keepBs : ∀ {p : Addr} {n : Nat}, (⟨p, 16 * n⟩ : Region).Disjoint (tR s) → 16 * n ≤ 2 ^ 64 →
      blocksAt (pushed [.rax, .r9, .r10] st).callEntry.mem p n = blocksAt st.mem p n := fun hd hn => by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, keep hd hn]
  have pr := pre_sub (s := s) hq
  have eC := keepB (hp.b_st.symm.sub_left ctr_sub)
  have eY := keepB (hp.b_st.symm.sub_left y_sub)
  have eS := keepBs (n := q) (hp.b_r.symm.sub_left (Offset.sub_base _ (by omega))) (by omega)
  have hqn : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := Proof.AesGcm.encryptBlocksToX86_64M M)
    T.ok T.sp (by have := T.xd; omega) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost, Proof.AesGcm.arg, a0,
    State.withRegions_mem, gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp),
    gU _ (by decide : Reg.rdx ≠ .rsp), gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp),
    gU _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, h_9, h_10, hqn, hm₂, ciph_eq hp fU, hk_eq hp fU,
    eC, eY, eS] at hpost
  obtain ⟨o₁, o₂, o₃⟩ := hpost
  refine ⟨r₃, hwr', fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    have b32 : Region.Sub (below ((pushed [.rax, .r9, .r10] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (tR s) := by
      have h₁ := below_sub (sp := (pushed [.rax, .r9, .r10] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8) (b := 32)
        (by have := T.xd; omega) (by decide)
      have e : below (SP s - BitVec.ofNat 64 24) 32 = ⟨SP s - BitVec.ofNat 64 56, 32⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨tR s, by simp, b32⟩
  · rw [popped_mem]; exact o₁
  · rw [popped_mem]; exact o₂
  · rw [popped_mem, o₁]; exact o₃

end

end VG.Proof.AesGcm.X86_64.StreamTo

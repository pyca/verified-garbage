module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops

/-! ### `AesGcm.X86_64.Split.Prefix`, which only this module used -/

section

/-!
# AES-GCM `seal_split` on x86-64: the whole blocks at `src`

Untrusted: everything here is checked by Lean. After `J₀` and the
additional data, `prefix` encrypts the `q = ⌊sl / 16⌋` whole blocks at `src`
to `dst` and absorbs them by a call of `vg_aes_gcm_encrypt_blocks_to` with
`dst`, `q` and its working space pushed for it (`preCall_ok`), copies the
`sl mod 16` bytes left to `dst` (`copyLoop`), and keeps `len` at `auxO` and
the data from those bytes on as the data (`prefix_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn covers_cons' covers_nil' sub_add_ofNat off_bound stackArg_entry)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- What `prefix` needs, after `J₀` and the additional data: the
environment, the slots it reads, the data `D` of `n` bytes, the `sl` bytes
at `S`, and the 56 bytes below `SP` apart from all of them. -/
structure PP (M : CtxMode) (Ctx W SP D S : Addr) (R n sl : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  lay : Lay Ctx (W + BitVec.ofNat 64 16) W SP
  rounds : RoundsAt s.mem W R
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  src : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S
  slen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl
  data : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  srcCov : Covers [⟨S, sl⟩] (s.rd ++ s.wr)
  sW : (⟨S, sl⟩ : Region).Disjoint ⟨W, 2560⟩
  sD : (⟨S, sl⟩ : Region).Disjoint ⟨D, n⟩
  sWrap : S.toNat + sl ≤ 2 ^ 64
  sl_le : sl ≤ n
  kw : (below SP 56).Disjoint ⟨W, 2560⟩
  kd : (below SP 56).Disjoint ⟨D, n⟩
  ks : (below SP 56).Disjoint ⟨S, sl⟩
  kM : (below SP 56).Disjoint ⟨Ctx, M.len⟩
  sp56 : 56 ≤ SP.toNat
  ext : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s

/-- A part of a region covered is covered. -/
theorem covers_off' {p : Addr} {k d m : Nat} {ts : List Region} (h : Covers [⟨p, k⟩] ts) (hd : d + m ≤ k)
    (hk : k < 2 ^ 64 := by decide) : Covers [⟨p + BitVec.ofNat 64 d, m⟩] ts := X86_64.covers_off h hd hk

/-- A prefix of a region covered is covered. -/
theorem covers_pre {p : Addr} {k m : Nat} {ts : List Region} (h : Covers [⟨p, k⟩] ts) (hm : m ≤ k) :
    Covers [⟨p, m⟩] ts := fun a j ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a j ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩

/-- Covered by a list, so by it after another region. -/
theorem covers_tail {rs ts : List Region} {r : Region} (h : Covers rs ts) : Covers rs (r :: ts) :=
  fun a j ⟨x, hx, hc⟩ => by
    obtain ⟨y, hy, hc'⟩ := h a j ⟨x, hx, hc⟩
    exact ⟨y, List.mem_cons_of_mem _ hy, hc'⟩

/-- Covered by `ts ++ us`, so by `ts ++ x :: us`. -/
theorem covers_ins {rs ts us : List Region} {x : Region} (h : Covers rs (ts ++ us)) : Covers rs (ts ++ x :: us) :=
  fun a j hx => by
    obtain ⟨y, hy, hc'⟩ := h a j hx
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨y, List.mem_append_left _ hy, hc'⟩
    · exact ⟨y, List.mem_append_right _ (List.mem_cons_of_mem _ hy), hc'⟩

theorem covers_right {rs ts us : List Region} (h : Covers rs us) : Covers rs (ts ++ us) :=
  fun a j hx => by
    obtain ⟨y, hy, hc'⟩ := h a j hx
    exact ⟨y, List.mem_append_right _ hy, hc'⟩

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
include h

omit h in
/-- A region of the stack below `SP - a`, in the 56 bytes below `SP`. -/
theorem stk56_sub {a k : Nat} (ha : a ≤ 56) (hk : k ≤ a) :
    Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ (below SP 56) := Offset.sub_below _ (by omega_arith) (by omega_arith)

/-- The regions the call reads and writes, for `q` whole blocks. -/
abbrev callRd (M : CtxMode) (Ctx SP S : Addr) (q : Nat) : List Region :=
  [⟨Ctx, M.len⟩, ⟨S, q * 16⟩, ⟨SP - BitVec.ofNat 64 24, 24⟩]
abbrev callWr (W D : Addr) (q : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩,
    ⟨D, q * 16⟩, ⟨W + BitVec.ofNat 64 448, 2112⟩]

/-- The counter block and `Y` of the state, and the working space of the call. -/
abbrev cbR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩
abbrev yR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩
abbrev scR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 448, 2112⟩

omit h in
theorem cb_sub : Region.Sub (cbR W) ⟨W + BitVec.ofNat 64 16, 80⟩ := Offset.sub_base _ (by decide)
omit h in
theorem y_sub : Region.Sub (yR W) ⟨W + BitVec.ofNat 64 16, 80⟩ := Offset.sub_base _ (by decide)
omit h in
theorem st_w : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ ⟨W, 2560⟩ := Lay.wSub (by decide)
omit h in
theorem sc_w : Region.Sub (scR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
omit h in
theorem sc_b : Region.Sub (scR W) ⟨W + BitVec.ofNat 64 96, 2464⟩ := Offset.sub _ (by decide) (by decide)

/-- What the call of `vg_aes_gcm_encrypt_blocks_to` needs, at its entry. -/
theorem callPre {q : Nat} (hq : 16 * q ≤ sl) {u : State}
    (hrsp : u.gpr .rsp = SP - BitVec.ofNat 64 32) (hrd : u.rd = callRd M Ctx SP S q) (hwr : u.wr = callWr W D q)
    (h_di : u.gpr .rdi = Ctx) (h_si : u.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : u.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : u.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : u.gpr .r8 = S)
    (h_9 : u.gpr .r9 = BitVec.ofNat 64 q) (a0 : stackArg u 0 = D) (a1 : stackArg u 1 = BitVec.ofNat 64 q)
    (a2 : stackArg u 2 = W + BitVec.ofNat 64 448) (hok : M.ok u.mem Ctx) :
    (Proof.AesGcm.encryptBlocksToX86_64M M).pre u := by
  have L := h.lay
  have hn := h.data.ok.lt
  obtain sl64 : sl < 2 ^ 64 := by have := h.sl_le; omega_arith
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain hRn : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)
  have sp := h.sp56
  obtain hargs : (Proof.AesGcm.args u 3) = ⟨SP - BitVec.ofNat 64 24, 24⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  obtain hret : (Proof.AesGcm.ret u) = ⟨SP - BitVec.ofNat 64 32, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  obtain hstk : (Proof.AesGcm.stk24 u) = ⟨SP - BitVec.ofNat 64 56, 24⟩ := by
    simp only [Proof.AesGcm.stk24, below, hrsp]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  obtain tA : Region.Sub ⟨SP - BitVec.ofNat 64 24, 24⟩ (below SP 56) := stk56_sub (by decide) (by decide)
  obtain tR' : Region.Sub ⟨SP - BitVec.ofNat 64 32, 8⟩ (below SP 56) := stk56_sub (by decide) (by decide)
  obtain tS : Region.Sub ⟨SP - BitVec.ofNat 64 56, 24⟩ (below SP 56) := stk56_sub (by decide) (by decide)
  obtain pr : Region.Sub ⟨S, q * 16⟩ ⟨S, sl⟩ := Region.sub_prefix (by omega_arith)
  obtain ds : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by have := h.sl_le; omega_arith)
  obtain cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  obtain yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  obtain ws : (W + BitVec.ofNat 64 448).toNat = W.toNat + 448 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 448) (by decide)]
    have := L.ww; omega_arith
  obtain st16 : (W + BitVec.ofNat 64 16).toNat = W.toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide)]
    have := L.ww; omega_arith
  obtain st48 : (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48).toNat = W.toNat + 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide), st16]
    have := L.ww; omega_arith
  obtain st32 : (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16).toNat = W.toNat + 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), st16]
    have := L.ww; omega_arith
  obtain hsp32 : (SP - BitVec.ofNat 64 32).toNat = SP.toNat - 32 := toNat_sub_ofNat (by omega_arith)
  obtain dS := h.sW.sub_left pr
  obtain dD := h.data.ok.w.sub_left ds
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPreM, Proof.AesGcm.arg, hargs, hret,
    hstk, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0, a1, a2, hqn, hrsp, Proof.AesGcm.rounds, hRn]
  refine ⟨trivial, trivial, trivial, h.ext.cs.sub_right cb_sub, h.ext.cs.sub_right y_sub, h.ext.cd.sub_right ds,
    h.ext.cw.sub_right sc_w,
    Offset.disjoint _ (.inr (by decide)) (by have := L.sw; omega_arith) (by have := L.sw; omega_arith),
    (dS.sub_right cW).symm, (dD.sub_right cW).symm, (L.sb.sub_left cb_sub).sub_right sc_b,
    (h.kw.sub_right cW).symm.sub_right tA,
    (dS.sub_right yW).symm, (dD.sub_right yW).symm, (L.sb.sub_left y_sub).sub_right sc_b,
    (h.kw.sub_right yW).symm.sub_right tA,
    (h.sD.sub_left pr).sub_right ds, dS.sub_right sc_w, dD.sub_right sc_w,
    (h.kd.sub_right ds).symm.sub_right tA, (h.kw.sub_right sc_w).symm.sub_right tA,
    (h.kw.sub_left tR').sub_right cW, (h.kw.sub_left tR').sub_right yW, (h.kd.sub_left tR').sub_right ds,
    (h.kw.sub_left tR').sub_right sc_w,
    h.kM.sub_left tS, (h.kw.sub_left tS).sub_right cW, (h.kw.sub_left tS).sub_right yW,
    (h.ks.sub_left tS).sub_right pr, (h.kd.sub_left tS).sub_right ds, (h.kw.sub_left tS).sub_right sc_w,
    h.ext.w, by rw [st48]; have := L.ww; omega_arith, by rw [st32]; have := L.ww; omega_arith, by have := h.sWrap; omega_arith,
    by have := h.data.ok.wrap; have := h.sl_le; omega_arith, by rw [ws]; have := L.ww; omega_arith,
    by rw [hsp32]; omega_arith, by rw [hsp32]; omega_arith, h.rounds.2, hok⟩

/-- The state the call of `vg_aes_gcm_encrypt_blocks_to` starts from. -/
abbrev callU (M : CtxMode) (Ctx W SP D S : Addr) (q : Nat) (st : State) : State :=
  (pushed [.rax, .r10, .r11] st).callEntry.withRegions (callRd M Ctx SP S q) (callWr W D q)

/-- What the call of `vg_aes_gcm_encrypt_blocks_to` starts from: its
precondition, the regions it may access, and its arguments. -/
theorem callIn {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = BitVec.ofNat 64 q) (h_11 : st.gpr .r11 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    (Proof.AesGcm.encryptBlocksToX86_64M M).pre (callU M Ctx W SP D S q st) ∧
      Covers (callRd M Ctx SP S q ++ callWr W D q)
        ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) ∧
      Covers (callWr W D q) (pushed [.rax, .r10, .r11] st).wr ∧
      (∀ r, r ≠ .rsp → (callU M Ctx W SP D S q st).gpr r = st.gpr r) ∧
      (callU M Ctx W SP D S q st).gpr .rsp = SP - BitVec.ofNat 64 32 ∧
      stackArg (callU M Ctx W SP D S q st) 0 = D ∧ stackArg (callU M Ctx W SP D S q st) 1 = BitVec.ofNat 64 q ∧
      stackArg (callU M Ctx W SP D S q st) 2 = W + BitVec.ofNat 64 448 := by
  have L := h.lay
  have sp := h.sp56
  have hn := h.data.ok.lt
  obtain hqs : q * 16 ≤ sl := by omega_arith
  obtain hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  obtain hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r10, .r11] st).mem.readW (SP - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r10, .r11][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  obtain hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain b56 : ∀ {a k : Nat}, a ≤ 56 → k ≤ a → ∃ r ∈ [below SP 56], Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ r :=
    fun ha hk => ⟨_, List.mem_singleton_self _, stk56_sub ha hk⟩
  obtain fS : Frame [below SP 56] st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf'.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide)).trans
      (hE.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide))
  obtain hPsp8 : 8 ≤ (SP - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP - BitVec.ofNat 64 24).toNat = SP.toNat - 24 := toNat_sub_ofNat (by omega_arith)
  obtain ea : ∀ i, i < 3 → stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (callRd M Ctx SP S q)
      (callWr W D q)) i =
      (pushed [.rax, .r10, .r11] st).mem.readW (SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * i)) 64 :=
    fun i hi => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith)
  obtain a0 := ea 0 (by decide)
  obtain a1 := ea 1 (by decide)
  obtain a2 := ea 2 (by decide)
  rw [show SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  obtain gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (callRd M Ctx SP S q) (callWr W D q)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (callRd M Ctx SP S q) (callWr W D q)).gpr .rsp =
      SP - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have kM := h.kM
  obtain hok : M.ok ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (callRd M Ctx SP S q) (callWr W D q)).mem Ctx := by
    rw [State.withRegions_mem]
    exact M.frame fS (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kM.symm) h.ext.w
      (hm ▸ h.ext.ok)
  obtain hpre := callPre h hq hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_cx) (by rw [gU _ (by decide)]; exact h_8)
    (by rw [gU _ (by decide)]; exact h_9) (by rw [a0, h_11]) (by rw [a1, h_10]) (by rw [a2, h_ax]) hok
  obtain hPw : (pushed [.rax, .r10, .r11] st).wr = ⟨SP - BitVec.ofNat 64 24, 24⟩ :: s.wr := by
    rw [pushed_wr, hsp, hwr]; rfl
  obtain hPr : (pushed [.rax, .r10, .r11] st).rd = s.rd := by rw [pushed_rd, hrd]
  have perm := h.env.perm
  obtain cC : Covers [cbR W] s.wr := covers_off' perm.st (show 48 + 16 ≤ 80 by decide)
  obtain cY : Covers [yR W] s.wr := covers_off' perm.st (show 16 + 16 ≤ 80 by decide)
  obtain cSc : Covers [scR W] s.wr := covers_off' perm.w (show 448 + 2112 ≤ 2560 by decide)
  obtain cD : Covers [⟨D, q * 16⟩] s.wr := covers_pre h.data.wr (by have := h.sl_le; omega_arith)
  obtain cR : Covers [⟨S, q * 16⟩] (s.rd ++ s.wr) := covers_pre h.srcCov hqs
  have cK : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr) := h.ext.cov
  obtain cw : Covers (callWr W D q) (pushed [.rax, .r10, .r11] st).wr := by
    rw [hPw]
    exact covers_cons' (covers_tail cC) (covers_cons' (covers_tail cY) (covers_cons' (covers_tail cD)
      (covers_cons' (covers_tail cSc) covers_nil')))
  obtain cr : Covers (callRd M Ctx SP S q ++ callWr W D q)
      ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_ins cK) (covers_cons' (covers_ins cR)
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_right (covers_tail cC))
      (covers_cons' (covers_right (covers_tail cY)) (covers_cons' (covers_right (covers_tail cD))
      (covers_cons' (covers_right (covers_tail cSc)) covers_nil'))))))
  exact ⟨hpre, cr, cw, gU, hU, a0.trans h_11, a1.trans h_10, a2.trans h_ax⟩

/-- The call of `vg_aes_gcm_encrypt_blocks_to` on the `q` whole blocks at
`S`, to `D`, with `D`, `q` and the working space pushed for it. -/
theorem preCall_ok (T : BlkToFn M) {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = BitVec.ofNat 64 q) (h_11 : st.gpr .r11 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (callWr W D q ++ [below SP 56]) st.mem st'.mem ∧
      blocksAt st'.mem D q = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))
        (blocksAt s.mem S q) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
        ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt st'.mem D q) := by
  have L := h.lay
  have sp := h.sp56
  have hn := h.data.ok.lt
  obtain hqs : q * 16 ≤ sl := by omega_arith
  obtain hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  obtain hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain b56 : ∀ {a k : Nat}, a ≤ 56 → k ≤ a → ∃ r ∈ [below SP 56], Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ r :=
    fun ha hk => ⟨_, List.mem_singleton_self _, stk56_sub ha hk⟩
  obtain fS : Frame [below SP 56] st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf'.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide)).trans
      (hE.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide))
  have kM := h.kM
  obtain ⟨hpre, cr, cw, gU, -, a0, -, -⟩ := callIn h hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_11 h_ax
  -- What the push and the return address leave as it was.
  obtain keep : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint (below SP 56) → k ≤ 2 ^ 64 →
      bytesAt (pushed [.rax, .r10, .r11] st).callEntry.mem p k = bytesAt s.mem p k := fun hd hk => by
    rw [← hm]
    exact bytesAt_frame fS (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hk
  obtain keepB : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint (below SP 56) →
      blockAt (pushed [.rax, .r10, .r11] st).callEntry.mem p = blockAt s.mem p := fun hd => by
    rw [blockAt, blockAt, keep hd (by decide)]
  obtain cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  obtain yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  obtain eC := keepB ((h.kw.sub_right cW).symm)
  obtain eY := keepB ((h.kw.sub_right yW).symm)
  obtain eS : blocksAt (pushed [.rax, .r10, .r11] st).callEntry.mem S q = blocksAt s.mem S q := by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq,
      keep ((h.ks.sub_right (Region.sub_prefix (by omega_arith))).symm) (by have := h.sWrap; omega_arith)]
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  obtain eK : ctxCiph (pushed [.rax, .r10, .r11] st).callEntry.mem Ctx R = ctxCiph s.mem Ctx R := by
    simp only [ctxCiph]
    rw [keep ((kM.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge))).symm) (Nat.le_trans hRb (by decide))]
  obtain eH : ctxH (pushed [.rax, .r10, .r11] st).callEntry.mem Ctx = ctxH s.mem Ctx := by
    simp only [ctxH]
    exact keepB ((kM.sub_right (Offset.sub_base _ (by have := M.ge; omega_arith))).symm)
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.sl_le; omega_arith)
  obtain hRn : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := Proof.AesGcm.encryptBlocksToX86_64M M)
    T.ok T.sp (by have := T.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost, Proof.AesGcm.arg, a0,
    State.withRegions_mem, gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp),
    gU _ (by decide : Reg.rdx ≠ .rsp), gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp),
    gU _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, h_9, h_11, hqn, hRn, hm₂, eK, eH,
    eC, eY, eS] at hpost
  obtain ⟨o₁, o₂, o₃⟩ := hpost
  refine ⟨r₃, hwr', fun m u fm => ?_⟩
  -- The `pop` loses the frame's 24 bytes, in the stack below `SP`, apart from
  -- the outputs.
  obtain fm' : Frame [below SP 56] s'.mem m := by
    rw [hsp] at fm
    exact fm.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact b56 (by decide) (by decide)
  obtain one : ∀ {r : Region}, (below SP 56).Disjoint r → ∀ r' ∈ [below SP 56], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.symm
  obtain kD : blocksAt m D q = blocksAt s'.mem D q :=
    blocksAt_frame fm' (one (h.kd.sub_right (Region.sub_prefix (by have := h.sl_le; omega_arith))))
      (by have := h.data.ok.wrap; have := h.sl_le; omega_arith)
  obtain kC := blockAt_frame fm' (one (h.kw.sub_right cW))
  obtain kY := blockAt_frame fm' (one (h.kw.sub_right yW))
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · refine Frame.trans ?_ (fm'.sub fun r hr => ⟨below SP 56, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
    obtain bT : Region.Sub (below ((pushed [.rax, .r10, .r11] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (below SP 56) := by
      obtain h₁ := below_sub (sp := (pushed [.rax, .r10, .r11] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8) (b := 32)
        (by have := T.xd; omega_arith) (by decide)
      obtain e : below (SP - BitVec.ofNat 64 24) 32 = ⟨SP - BitVec.ofNat 64 56, 32⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h' => stk56_sub (by decide) (by decide) a (h₁ a h')
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below SP 56, by simp, stk56_sub (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below SP 56, by simp, bT⟩
  · rw [kD]; exact o₁
  · rw [kC]; exact o₂
  · rw [kY, kD, o₁]; exact o₃

end

/-! ## The blocks around the call -/

section
variable {Ctx W SP : Addr}

/-- The number of whole blocks at `src`, `ZF` if none. -/
theorem pre1_ok {sl : Nat} (hsl : sl < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.preTest) s fun s₁ => s₁.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧
      s₁.zf = some (decide (sl / 16 = 0)) ∧ (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain h4 := shr4 sl hsl
  obtain hz := and_self_beq (show sl / 16 < 2 ^ 64 by omega_arith)
  unfold SealSplit.preTest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, hslot, h4], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- The arguments of the call. -/
theorem pre2_ok {R : Nat} {D S : Addr} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S) :
    WP isa (.block SealSplit.preArgs) s fun s₂ => s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧
      s₂.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48 ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16 ∧ s₂.gpr .r8 = S ∧ s₂.gpr .r9 = s.gpr .rax ∧
      s₂.gpr .r10 = s.gpr .rax ∧ s₂.gpr .r11 = D ∧ s₂.gpr .rax = W + BitVec.ofNat 64 448 ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₂.gpr r = s.gpr r) ∧
      s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  unfold SealSplit.preArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r13, he.r14, he.r15, q₁, q₂, q₃, hR.1, hdat, hsrc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, he.r13]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hR.1]
  · simp [gpr_setReg, gpr_arithFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hsrc]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, hdat]
  · simp [gpr_setReg, gpr_arithFlags, he.r15, imm_eq, bScrO]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The bytes left at `src` after its whole blocks: their number, `ZF` if
none, and their address and that of their copy. -/
theorem pre3_ok {D S : Addr} {sl : Nat} (hsl : sl < 2 ^ 64) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.copyArgs) s fun s₃ => s₃.gpr .rcx = BitVec.ofNat 64 (sl % 16) ∧
      s₃.gpr .rsi = S + BitVec.ofNat 64 (16 * (sl / 16)) ∧ s₃.gpr .rdi = D + BitVec.ofNat 64 (16 * (sl / 16)) ∧
      s₃.zf = some (decide (sl % 16 = 0)) ∧ (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₃.gpr r = s.gpr r) ∧
      s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain e15 := and15 (BitVec.ofNat 64 sl)
  rw [toNat_ofNat_of_lt hsl, imm_eq (by decide)] at e15
  obtain esub : BitVec.ofNat 64 sl - BitVec.ofNat 64 (sl % 16) = BitVec.ofNat 64 (16 * (sl / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hsl]; congr 1; omega_arith
  obtain hz := and_self_beq (show sl % 16 < 2 ^ 64 by omega_arith)
  unfold SealSplit.copyArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, hslot, hdat, hsrc, e15, esub], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, e15]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, esub, hsrc]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, esub, hdat]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, e15, hz]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- `len` kept at `auxO`, and the data from `16 ⌊sl / 16⌋` on as the data. -/
theorem pre4_ok {D : Addr} {n sl : Nat} (hn : n < 2 ^ 64) (hsl : sl ≤ n) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.rest) s fun s₄ =>
      s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (sl / 16)) ∧
      s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (sl / 16)) ∧
      s₄.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      Frame [⟨W + BitVec.ofNat 64 200, 24⟩] s.mem s₄.mem ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
  have hsl' : sl < 2 ^ 64 := by omega_arith
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 sl)
  rw [toNat_ofNat_of_lt hsl', imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 sl - BitVec.ofNat 64 (sl % 16) = BitVec.ofNat 64 (16 * (sl / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hsl']; congr 1; omega_arith
  have esub' : BitVec.ofNat 64 n - BitVec.ofNat 64 (16 * (sl / 16)) = BitVec.ofNat 64 (n - 16 * (sl / 16)) :=
    ofNat_sub (by omega_arith) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by have := he.perm; omega_arith) (by omega_arith)
  have p₁ := sep 216 208 (by decide) (by decide) (by decide)
  have p₂ := sep 216 200 (by decide) (by decide) (by decide)
  have p₃ := sep 208 200 (by decide) (by decide) (by decide)
  have p₄ := sep 200 208 (by decide) (by decide) (by decide)
  have p₅ := sep 200 216 (by decide) (by decide) (by decide)
  have p₆ := sep 208 216 (by decide) (by decide) (by decide)
  have hdat' : ((s.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 n)).writeW (W + BitVec.ofNat 64 208)
      (BitVec.ofNat 64 (n - 16 * (sl / 16)))).readW (W + BitVec.ofNat 64 200) 64 = D := by
    rw [Mem.readW_writeW_sep p₄ (by decide), Mem.readW_writeW_sep p₅ (by decide), hdat]
  unfold SealSplit.rest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, w₁, w₂, w₃, hslot, hlen, e15, esub, esub', hdat'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mem_arithFlags, mem_setReg, Mem.readW_writeW_self64, BitVec.add_comm]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep p₃ (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep p₂ (by decide), Mem.readW_writeW_sep p₁ (by decide), Mem.readW_writeW_self64]
  · have c : ∀ d, 200 ≤ d → d + 8 ≤ 224 → (⟨W + BitVec.ofNat 64 200, 24⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by have := he.perm; omega_arith)
    simp only [mem_arithFlags, mem_setReg]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

end VG.Proof.AesGcm.X86_64.Split

end

end


/-!
# AES-GCM `seal_split` on x86-64: `prefix`

Untrusted: everything here is checked by Lean. `prefix` leaves the
`q = ⌊sl / 16⌋` whole blocks at `src` encrypted to `dst` and absorbed, the
counter block advanced by `q`, the `sl mod 16` bytes left copied after them,
`len` kept at `auxO` and the data from those bytes on as the data
(`prefix_ok`), having written only the counter block and `Y`, the blocks and
the bytes copied, the slots it keeps, the call's working space and the 56
bytes below `SP`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The counter block and `Y` of the state. -/
abbrev cbA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
abbrev yA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16

/-- After the call (or none, for no whole block): what it did. -/
structure Mid2 (Ctx W SP D S : Addr) (R sl : Nat) (s s₂ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [below SP 56]) s.mem s₂.mem
  blocks : blocksAt s₂.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s₂.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s₂.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s₂.mem D (sl / 16))

/-- What `prefix` leaves. -/
structure PPost (Ctx W SP D S : Addr) (R n sl : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩,
    ⟨W + BitVec.ofNat 64 200, 24⟩, below SP 56]) s.mem s'.mem
  blocks : blocksAt s'.mem D (sl / 16) = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16))
  ctr : blockAt s'.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W))
  y : blockAt s'.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s'.mem D (sl / 16))
  tail : bytesAt s'.mem (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
    bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (sl / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (sl / 16))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
include h

/-- A slot of `W` from `W + 128` on is apart from what the call writes. -/
theorem slot_disj {q d : Nat} (hq : q * 16 ≤ n) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 448) :
    ∀ r ∈ callWr W D q ++ [below SP 56], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have L := h.lay
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact ((h.data.ok.w.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by omega_arith))).symm
  · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (h.kw.sub_right (Lay.wSub (by omega_arith))).symm

/-- `src` is apart from what the call writes. -/
theorem src_disj {q : Nat} (hq : q * 16 ≤ n) {p : Addr} {k : Nat} (hs : Region.Sub ⟨p, k⟩ ⟨S, sl⟩) :
    ∀ r ∈ callWr W D q ++ [below SP 56], (⟨p, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact (h.sW.sub_left hs).sub_right (fun a hc => st_w a (cb_sub a hc))
  · exact (h.sW.sub_left hs).sub_right (fun a hc => st_w a (y_sub a hc))
  · exact (h.sD.sub_left hs).sub_right (Region.sub_prefix hq)
  · exact (h.sW.sub_left hs).sub_right sc_w
  · exact (h.ks.sub_right hs).symm

/-- A slot of `W` from `W + 128` on is apart from what the call and the copy write. -/
theorem slot_disj2 {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 448) :
    ∀ r ∈ callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hsl := h.sl_le
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slot_disj h (by omega_arith) h₁ h₂ r (List.mem_append_left _ hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((h.data.ok.w.sub_left (Offset.sub_base D (by omega_arith))).sub_right (Lay.wSub (by omega_arith))).symm
    · exact slot_disj h (q := sl / 16) (by omega_arith) h₁ h₂ _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- `rest`, after the bytes left are copied (or none): what `prefix` leaves. -/
theorem rest_ok {s₄ : State} (he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄) (rd₄ : s₄.rd = s.rd)
    (wr₄ : s₄.wr = s.wr)
    (fr₄ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem s₄.mem)
    (bl₄ : blocksAt s₄.mem D (sl / 16) =
      ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (cbA W)) (blocksAt s.mem S (sl / 16)))
    (ct₄ : blockAt s₄.mem (cbA W) = Nat.repeat inc32 (sl / 16) (blockAt s.mem (cbA W)))
    (y₄ : blockAt s₄.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s₄.mem D (sl / 16)))
    (tl₄ : bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) :
    WP isa (.block SealSplit.rest) s₄ (PPost Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  obtain kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fr₄.readW (Region.contains_self _ _) (slot_disj2 h h₁ h₂) (by decide)
  refine WP.mono (pre4_ok (D := D) hn hsl he₄ (by rw [kp 200 (by decide) (by decide)]; exact h.dat)
    (by rw [kp 208 (by decide) (by decide)]; exact h.len) (by rw [kp 192 (by decide) (by decide)]; exact h.slen))
    fun s₅ ⟨d₅, l₅, a₅, f₅, g₅, rd₅, wr₅⟩ => ?_
  obtain W200 : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 24⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (Lay.wSub (by decide))
  obtain dB : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W, 2560⟩ := h.data.ok.w.sub_left (Region.sub_prefix (by omega_arith))
  obtain dT : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    h.data.ok.w.sub_left (Offset.sub_base D (by omega_arith))
  obtain cW : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 200, 24⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 24⟩ : Region)], (⟨p, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain eB : blocksAt s₅.mem D (sl / 16) = blocksAt s₄.mem D (sl / 16) :=
    blocksAt_frame f₅ (W200 dB) (by omega_arith)
  obtain eC : blockAt s₅.mem (cbA W) = blockAt s₄.mem (cbA W) :=
    blockAt_frame f₅ (cW (by simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  obtain eY : blockAt s₅.mem (yA W) = blockAt s₄.mem (yA W) :=
    blockAt_frame f₅ (cW (by simp only [yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))
  refine ⟨he₄.keep g₅ rd₅ wr₅, rd₅.trans rd₄, wr₅.trans wr₄, ?_, by rw [eB, bl₄], by rw [eC, ct₄],
    by rw [eY, eB, y₄], by rw [bytesAt_frame f₅ (W200 dT) (by omega_arith), tl₄], d₅, l₅, a₅⟩
  refine (fr₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, fun _ h => h⟩

/-- After the call (or none): the bytes left copied, and `rest`. -/
theorem tail_ok {s₂ : State} (H : Mid2 Ctx W SP D S R sl s s₂) :
    WP isa (.seq (.block SealSplit.copyArgs) (.seq (.ite .e (.block []) copyLoop) (.block SealSplit.rest))) s₂
      (PPost Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  obtain kp : ∀ d, 128 ≤ d → d + 8 ≤ 448 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => H.frame.readW (Region.contains_self _ _) (slot_disj h (q := sl / 16) (by omega_arith) h₁ h₂) (by decide)
  refine WP.seq (WP.mono (pre3_ok (D := D) (S := S) (sl := sl) (by omega_arith) H.env (by rw [kp 200 (by decide) (by decide)]; exact h.dat)
    (by rw [kp 224 (by decide) (by decide)]; exact h.src) (by rw [kp 192 (by decide) (by decide)]; exact h.slen))
    fun s₃ ⟨cx₃, si₃, di₃, zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := H.env.keep g₃ rd₃ wr₃
  obtain fr₂ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem s₂.mem := H.frame.mono fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · simp only [List.mem_singleton] at hr; subst hr; simp
  obtain hs₂ : bytesAt s₂.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) :=
    bytesAt_frame H.frame (src_disj h (q := sl / 16) (by omega_arith) (Offset.sub_base S (by omega_arith))) (by omega_arith)
  refine WP.seq (WP.ite (decide (sl % 16 = 0)) (by simp only [eval, zf₃]) (fun h0 => ?_) (fun h0 => ?_))
  · have h0' : sl % 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (rest_ok h he₃ (rd₃.trans H.rd) (wr₃.trans H.wr) (by rw [m₃]; exact fr₂)
      (by rw [m₃]; exact H.blocks) (by rw [m₃]; exact H.ctr) (by rw [m₃]; exact H.y) ?_)
    rw [h0']; rfl
  · have h0' : sl % 16 ≠ 0 := of_decide_eq_false h0
    obtain e1 : 16 * (sl / 16) + sl % 16 ≤ sl := by omega_arith
    obtain e2 : 16 * (sl / 16) + sl % 16 ≤ n := by omega_arith
    obtain sl64 : sl < 2 ^ 64 := by omega_arith
    obtain c1 : Covers [⟨S + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] (s₃.rd ++ s₃.wr) := by
      rw [rd₃, wr₃, H.rd, H.wr]; exact covers_off' h.srcCov e1 sl64
    obtain c2 : Covers [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] s₃.wr := by
      rw [wr₃, H.wr]; exact covers_off' h.data.wr e2 hn
    obtain hlp : LoopPre s₃ (S + BitVec.ofNat 64 (16 * (sl / 16))) (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) :=
      ⟨si₃, di₃, cx₃, by omega_arith, by omega_arith, c1, c2,
        (h.sD.sub_left (Offset.sub_base S (by omega_arith))).sub_right (Offset.sub_base D (by omega_arith))⟩
    refine WP.mono (copyLoop_ok s₃ hlp) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
    obtain he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) rd₄ wr₄
    obtain fC : Frame [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩] s₃.mem s₄.mem := by
      rw [m₄]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
    obtain one : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ →
        ∀ r ∈ [(⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r :=
      fun hd r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd
    have dDT := h.data.ok.w
    obtain dBT : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ := by
      have hw := h.data.ok.wrap
      simpa using Offset.disjoint D (d := 0) (n := 16 * (sl / 16)) (e := 16 * (sl / 16))
        (k := sl % 16) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    obtain eB : blocksAt s₄.mem D (sl / 16) = blocksAt s₃.mem D (sl / 16) :=
      blocksAt_frame fC (one dBT) (by omega_arith)
    obtain tW : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
      dDT.sub_left (Offset.sub_base D (by omega_arith))
    obtain eC : blockAt s₄.mem (cbA W) = blockAt s₃.mem (cbA W) :=
      blockAt_frame fC (one ((tW.sub_right (fun a hc => st_w a (cb_sub a hc))).symm))
    obtain eY : blockAt s₄.mem (yA W) = blockAt s₃.mem (yA W) :=
      blockAt_frame fC (one ((tW.sub_right (fun a hc => st_w a (y_sub a hc))).symm))
    obtain fC' : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
        s₂.mem s₄.mem := by
      rw [← m₃]
      exact fC.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    refine rest_ok h he₄ (rd₄.trans (rd₃.trans H.rd)) (wr₄.trans (wr₃.trans H.wr)) (fr₂.trans fC')
      (by rw [eB, m₃]; exact H.blocks) (by rw [eC, m₃]; exact H.ctr) (by rw [eY, eB, m₃]; exact H.y) ?_
    rw [m₄]
    have := bytesAt_writeBytes_self s₃.mem (D + BitVec.ofNat 64 (16 * (sl / 16)))
      (bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at this
    rw [this, m₃, hs₂]

/-- The call of `prefix` for the `sl / 16` whole blocks at `src`, from a
state `s₁` with their number in `rax` and `s`'s memory: what `Mid2` says. -/
theorem call_ok (T : BlkToFn M) {s₁ : State} (he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁)
    (ax₁ : s₁.gpr .rax = BitVec.ofNat 64 (sl / 16)) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd)
    (wr₁ : s₁.wr = s.wr) :
    WP isa (.seq (.block SealSplit.preArgs)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3))) s₁
      (Mid2 Ctx W SP D S R sl s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  refine WP.seq (WP.mono (pre2_ok (R := R) (D := D) (S := S) he₁ (by rw [m₁]; exact h.rounds) (by rw [m₁]; exact h.dat)
    (by rw [m₁]; exact h.src)) fun s₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep g₂ rd₂ wr₂
  exact WP.mono (preCall_ok h T (q := sl / 16) (by omega_arith) he₂.rsp (rd₂.trans rd₁) (wr₂.trans wr₁)
    (m₂.trans m₁) di₂ si₂ dx₂ cx₂ r8₂ (by rw [r9₂, ax₁]) (by rw [r10₂, ax₁]) r11₂ ax₂)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he₂.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), by rw [m₂, m₁] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

/-- `prefix`: the whole blocks at `src` encrypted to `dst` and absorbed by a
call of `vg_aes_gcm_encrypt_blocks_to` (`T`), the bytes left copied, and
`len` and the data from them on kept. -/
theorem prefix_ok (T : BlkToFn M) :
    WP isa (SealSplit.prefix T.fn) s (PPost Ctx W SP D S R n sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have he := h.env
  unfold SealSplit.prefix
  refine WP.seq (WP.mono (pre1_ok (sl := sl) (by omega_arith) he h.slen) fun s₁ ⟨ax₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine WP.seq (WP.ite (decide (sl / 16 = 0)) (by simp only [eval, zf₁]) (fun h0 => ?_) (fun h0 => ?_))
  · -- No whole block at `src`.
    obtain h0' : sl / 16 = 0 := of_decide_eq_true h0
    refine WP.block_nil (tail_ok h ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_, ?_⟩)
    · rw [h0']; rfl
    · rw [h0', m₁]; rfl
    · rw [h0', m₁]; rfl
  · exact WP.mono (call_ok h T he₁ ax₁ m₁ rd₁ wr₁) fun _ H => tail_ok h H

end

end VG.Proof.AesGcm.X86_64.Split

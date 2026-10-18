module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SShape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the frame's shape through `signMain`

Each piece of `signMain` leads from one `SS` to the next, by its
correctness lemma, of which only the frame's shape, the slots it sets and the
registers the next piece reads are kept: what the constant-time proof needs
of one run between the pieces. The last, `privArgs`, leads to the call's
precondition (`SSet`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sHD sK oEm oSt oDig oBuf oW oRsa scr lay clearEm)
open VG.Impl.Mgf1.X86_64 (sp ix at_ byteLoop mgfXor initF updF finF)
open VG.Proof.RsaOaep.X86_64 (decStack fb Lay Rep upd nW tw lenOf FnsD wp_good block_good keep_cs3 sizes scr_ok
  initF_ok updF_ok updExtF_ok finF_ok mgfXor_ok mW_args mW_other clearEm_good clearEm_ok rdIn_entry ret_subD)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

/-- After the checks. -/
def JMS (s t : State) : Prop :=
  SEnv s t ∧ Lay t (fb s) (stackArg s 14) ∧ Rep t.mem (fb s) (stackArg s 14) (sv0 s) (scW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (sk s - loV (sn0v s) - (lenOf (sselH s) + 2)) ∧ SFit s

theorem sdb_step {t : State} (h : JMS s t) : WP isa (.block dbSlots) t (SS PT s) := by
  obtain ⟨he, L, R, hax, hf⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, w31⟩ := scW_w s
  refine WP.mono (wp_good (block_good _ rfl rfl) (dbSlots_ok L R w31 hax))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ => ?_
  refine ⟨he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, ⟨_, _, R1, fun k hk => ?_,
    by simp [upd], by simp [upd], trivial⟩, hf⟩
  have := vKs_iff hk
  simp only [upd]; rw [ifn (show ¬ k = 33 by omega), ifn (show ¬ k = 44 by omega)]

theorem sclrEm_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : SS P s t) :
    WP isa clearEm t (SS P s) :=
  WP.mono (ss_stepW (X := fun _ => True) clearEm_good (rs := [.rcx, .rax, .r8]) (by decide) h
    fun _ _ R _ _ _ _ => WP.mono (clearEm_ok h.2.1 R) fun _ ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩)
    fun _ h => h.1

/-! ## The prefix and the hash calls' arguments -/

theorem smp_step {P : State → (Nat → BitVec 64) → Prop} (hp : SPre s) (hdl : (stackArg s 11).toNat = sgD s)
    {t : State} (h : SS P s t) : WP isa mPrefix t (SS P s) := by
  obtain ⟨-, -, hD16, hD64, -⟩ := h.2.2.2.sizes hp
  have hsl := hp.hsl
  have hwD := hp.wD
  have hwS := hp.wS
  have hk2 := hp.k2
  refine WP.mono (ss_stepW (X := fun _ => True) mPrefix_good (rs := [.rsi, .rcx, .r10, .rax, .r8]) (by decide) h
    fun V W R hA _ _ _ => ?_) fun _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, w27, -⟩ := hA.w
  have dgc : ∀ i < sgD s, (sdgR s).Contains (stackArg s 10 + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by rw [hdl]; omega) (by omega)
  exact WP.mono (mPrefix_ok h.2.1 R w27 hA.sel.1 (by omega) hD64
      (fun i hi => by
        rw [h.1.rd, hp.hrd]
        exact ⟨sdgR s, List.mem_append_left _ (by simp [srd]), dgc i hi⟩)
      (fun i hi j hj => VG.Proof.RsaOaep.X86_64.ne_of_disjoint hp.dds (dgc i hi)
        (Offset.contains_base _ (by unfold oMp; omega) (by unfold oMp; omega))))
    fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

/-- The state's address into `rdi`. -/
theorem sscr_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : SS P s t) :
    WP isa (.block (scr .rdi oSt)) t fun t' => SS P s t' ∧ t'.gpr .rdi = off (stackArg s 14) oSt :=
  ss_stepM (block_good _ rfl rfl) (rs := [.rdi]) (by decide) (by decide) h fun _ _ _ _ _ _ _ =>
    WP.mono (scr_ok h.2.1 (d := .rdi) (by decide) (o := oSt) (by decide)) fun _ ⟨a, b, c⟩ => ⟨b, c, a⟩

/-- The arguments of `update`, with the `len` bytes at `d`, after `cnt`. -/
def SRU (d : Addr) (len cnt : Nat) (s t : State) : Prop :=
  t.gpr .rdi = off (stackArg s 14) oSt ∧ t.gpr .rsi = BitVec.ofNat 64 cnt ∧ t.gpr .rdx = d ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .r8 = off (stackArg s 14) oW

/-- The arguments of `finalize`, to `scratch + o`, after `cnt`. -/
def SRF (o cnt : Nat) (s t : State) : Prop :=
  t.gpr .rdi = off (stackArg s 14) oSt ∧ t.gpr .rsi = BitVec.ofNat 64 cnt ∧ t.gpr .rdx = off (stackArg s 14) o ∧
    t.gpr .rcx = off (stackArg s 14) oW

theorem spre_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : SS P s t) :
    WP isa (.block (scr .rdi oSt ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ scr .rdx oMp ++
      ([.mov .rcx (.mem (sp sHD)), .alu .add .rcx (.imm 8)] : List Instr) ++ scr .r8 oW)) t
      fun t' => SS P s t' ∧ SRU (off (stackArg s 14) oMp) (sgD s + 8) 0 s t' :=
  ss_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx, .r8]) (by decide) (by decide) h
    fun _ _ R hA _ _ _ => WP.mono (updPre_ok h.2.1 R hA.sel.1) fun _ ⟨a, b, c, d, e, f, g⟩ =>
      ⟨f, g, a, b, c, d, e⟩

/-- Where the salt is. -/
theorem SPre.saltAt (hp : SPre s) {t : State} (he : SEnv s t) {W : Nat → BitVec 64} (hA : SArgs s W) :
    SaltAt t (fb s) (stackArg s 14) W (stackArg s 12) (ssl s) := by
  have hsl := hp.hsl
  have hwS := hp.wS
  have hk2 := hp.k2
  obtain ⟨-, -, -, -, -, -, -, -, w28, w29, -⟩ := hA.w
  exact ⟨w28, by rw [w29, BitVec.ofNat_toNat, BitVec.setWidth_eq], (stackArg s 13).isLt,
    VG.Covers.left (VG.Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr, he.rd, hp.hrd]; simp [srd]),
    hp.dsas.sub_right (Region.sub_prefix (by unfold oRsa; omega)), hp.dKsa.sub_left (ret_subD s)⟩

theorem ssalt_step {P : State → (Nat → BitVec 64) → Prop} (hp : SPre s) {t : State} (h : SS P s t) :
    WP isa (.block (scr .rdi oSt ++ plen ++
      ([.mov .rdx (.mem (sp sSalt)), .mov .rcx (.mem (sp sSaltLen))] : List Instr) ++ scr .r8 oW)) t
      fun t' => SS P s t' ∧ SRU (stackArg s 12) (ssl s) (sgD s + 8) s t' :=
  ss_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx, .r8]) (by decide) (by decide) h
    fun _ _ R hA _ _ _ => WP.mono (updSalt_ok h.2.1 R hA.sel.1 (hp.saltAt h.1 hA))
      fun _ ⟨a, b, c, d, e, f, g⟩ => ⟨f, g, a, b, c, d, e⟩

theorem sfinSl_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : SS P s t) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sSaltLen))] : List Instr) ++
      scr .rdx oDig ++ scr .rcx oW)) t fun t' => SS P s t' ∧ SRF oDig (sgD s + 8 + ssl s) s t' :=
  ss_stepM (block_good _ rfl rfl) (rs := [.rdi, .rsi, .rdx, .rcx]) (by decide) (by decide) h
    fun _ W R hA _ _ _ => by
      obtain ⟨-, -, -, -, -, -, -, -, -, w29, -⟩ := hA.w
      exact WP.mono (finSl_ok h.2.1 R hA.sel.1 (sl := ssl s)
          (by rw [w29, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (o := oDig) (by decide))
        fun _ ⟨a, b, c, d, e, f⟩ => ⟨e, f, a, b, c, d⟩

/-! ## The hash calls -/

section
variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)

include hT in
theorem sinit_step {P : State → (Nat → BitVec 64) → Prop} (fF : FnsD s T 18) {t : State} (h : SS P s t)
    (hdi : t.gpr .rdi = off (stackArg s 14) oSt) : WP isa (initF (8 * 45)) t (SS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.initF_good _) (initF_ok hT fF he.here L R (j := 45) rfl
    (by decide) hA.sel.2.2.1.1 hdi))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

include hT in
theorem supd_step {P : State → (Nat → BitVec 64) → Prop} (fF : FnsD s T 18) {t : State} (h : SS P s t)
    {a len cnt : Nat} (ha : a + len ≤ oRsa) (hda : a + len ≤ oSt ∨ oSt + T.S.stateBytes ≤ a)
    (hwa : a + len ≤ oW ∨ oW + 8 * T.scratch ≤ a) (hr : SRU (off (stackArg s 14) a) len cnt s t) :
    WP isa (updF (8 * 45)) t (SS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := hr
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.updF_good _) (updF_ok hT fF he.here L R (j := 45) rfl
    (by decide) hA.sel.2.2.1.2.1 ha hda hwa hdi hdx hcx h8))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

include hT in
/-- `update` with the salt, where it is. -/
theorem supdExt_step {P : State → (Nat → BitVec 64) → Prop} (hp : SPre s) (fF : FnsD s T 18) {t : State}
    (h : SS P s t) {cnt : Nat} (hr : SRU (stackArg s 12) (ssl s) cnt s t) : WP isa (updF (8 * 45)) t (SS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := hr
  have A := hp.saltAt he hA
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.updF_good _) (updExtF_ok hT fF he.here L R (j := 45) rfl
    (by decide) hA.sel.2.2.1.2.1 A.len hp.wSa (rdIn_entry (r := ssaR s) (by rw [hp.hrd]; simp [srd])) A.dS A.dK
    hdi hdx hcx h8))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

include hT in
theorem sfin_step {P : State → (Nat → BitVec 64) → Prop} (fF : FnsD s T 18) {t : State} (h : SS P s t)
    {o cnt : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW)) (hr : SRF o cnt s t) :
    WP isa (finF (8 * 45)) t (SS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  obtain ⟨hdi, -, hdx, hcx⟩ := hr
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.finF_good _) (finF_ok hT fF he.here L R (j := 45) rfl
    (by decide) hA.sel.2.2.1.2.2 ho hdi hdx hcx))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

end

/-! ## `EM` -/

theorem sputSalt_step {P : State → (Nat → BitVec 64) → Prop} (hp : SPre s) {t : State} (h : SS P s t) :
    WP isa putSalt t (SS P s) := by
  obtain ⟨-, d2, -, -, d5, d6, d7, -⟩ := h.2.2.2.sizes hp
  have e13 : ssl s = (stackArg s 13).toNat := rfl
  have c1 : oBuf = 1024 := rfl
  have hsl := hp.hsl
  have hwS := hp.wS
  have hwSa := hp.wSa
  have hk2 := hp.k2
  refine WP.mono (ss_stepW (X := fun _ => True) putSalt_good (rs := [.rdi, .rsi, .r10, .rax, .r8]) (by decide) h
    fun V W R hA h33 h44 _ => ?_) fun _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, -, w28, w29, -⟩ := hA.w
  have sac : ∀ i < ssl s, (ssaR s).Contains (stackArg s 12 + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  exact WP.mono (putSalt_ok h.2.1 R (e := sgE s) (db := sgDb s) (sl := ssl s) (q := stackArg s 12) h33 h44 w28
      (by rw [w29, BitVec.ofNat_toNat, BitVec.setWidth_eq]) d6 (by unfold oRsa; omega)
      (fun i hi => by rw [h.1.rd, hp.hrd]; exact ⟨ssaR s, List.mem_append_left _ (by simp [srd]), sac i hi⟩)
      (fun i hi j hj => VG.Proof.RsaOaep.X86_64.ne_of_disjoint hp.dsas (sac i hi)
        (Offset.contains_base _ (by omega) (by omega))))
    fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

theorem sputHd_step {P : State → (Nat → BitVec 64) → Prop} (hp : SPre s) {t : State} (h : SS P s t) :
    WP isa (.seq (.block (([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] : List Instr) ++
        scr .rsi oDig ++ ([.mov .r10 (.mem (sp sHD)), .mov32 .r8 (.imm 0)] : List Instr)))
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.reg .r10))) t (SS P s) := by
  obtain ⟨-, -, hD16, hD64, -, -, -, hend⟩ := h.2.2.2.sizes hp
  have hk2 := hp.k2
  refine WP.mono (ss_stepW (X := fun _ => True) ⟨rfl, rfl, by decide⟩ (rs := [.rdi, .rsi, .rax, .r8, .r10])
    (by decide) h fun V W R hA h33 h44 _ => ?_) fun _ h => h.1
  exact WP.mono (putHd_ok h.2.1 R (k := sk s) h33 h44 hA.sel.1 (by omega) hD64 hend hk2)
    fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

theorem sputBc_step {P : State → (Nat → BitVec 64) → Prop} (hp : SPre s) {t : State} (h : SS P s t) :
    WP isa (.block (scr .rdi oEm ++ ([.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .alu .sub .rdi (.imm 1),
        .mov32 .rax (.imm 0xbc), .store8 (at_ .rdi) .rax] : List Instr))) t (SS P s) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  refine WP.mono (ss_stepW (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rdi, .rax]) (by decide) h
    fun V W R hA _ _ _ => ?_) fun _ h => h.1
  obtain ⟨-, -, -, w23, -⟩ := hA.w
  exact WP.mono (putBc_ok h.2.1 R (k := sk s) (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (show 1 ≤ (s.gpr .rcx).toNat by omega) hk2)
    fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

/-- MGF1's slots, to mask `DB` with `H`. -/
def PMS (s : State) (W : Nat → BitVec 64) : Prop :=
  VG.Proof.RsaOaep.X86_64.MArgs W (stackArg s 14) (sgE s + sgDb s) (sgD s) (sgE s) (sgDb s)

theorem smgfArgs_step {t : State} (h : SS PT s t) : WP isa (.block mgfArgs) t (SS PMS s) :=
  WP.mono (ss_step (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rax, .rdx, .rcx, .r9]) (by decide) h
    fun _ _ R hA h33 h44 _ =>
    WP.mono (mgfArgs_ok h.2.1 R h33 h44 hA.sel.1) fun _ ⟨L', k', R'⟩ =>
      ⟨L', k', ⟨_, _, R', fun _ hk => mW_other (vkey_mW hk), mW_args _ _ _ _ _ _⟩, trivial⟩)
    fun _ h => h.1

section
variable {TG : Spec.HashFns.Streaming} {Gh : Spec.Mgf1.Hash} (hTG : StreamingOK TG Gh)

include hTG in
theorem smgf_step (hp : SPre s) (fG : FnsD s TG 19) (eG : Spec.HashId.mgf1 (sselG s) = some Gh) {t : State}
    (h : SS PMS s t) : WP isa (mgfXor lay) t (SS PT s) := by
  have hDG : TG.S.digestBytes = lenOf (sselG s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTG eG
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hM⟩, hf⟩ := h
  obtain ⟨d1, d2, -⟩ := hf.sizes hp
  refine WP.mono (wp_good VG.Proof.RsaOaep.X86_64.mgfXor_good (mgfXor_ok hTG fG (Gs := Gh)
      (fun x => by rw [hTG.hash]) hTG.len hTG.valid he.here L R
      ⟨by unfold oBuf oSt at *; omega, by unfold oBuf oSt at *; omega, .inr (Nat.le_refl _), d1,
        by unfold oBuf at d2; omega⟩ hM hA.sel.2.2.2 (by rw [hA.sel.2.1, hDG])))
    fun t' ⟨⟨L', _, rd', wr', cs', V', W', R', hW', _⟩, sp', mx', f'⟩ => ?_
  have hk : ∀ k, VKey k → W' k = W k := fun k hk =>
    hW' k (vkey_lt hk) (vkey_ne hk (by omega)) (vkey_ne hk (by omega))
  exact ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨V', W', R', fun k hk' => (hk k (.inl hk')).trans
    (hA k hk'), (hk 33 (.inr (.inl rfl))).trans h33, (hk 44 (.inr (.inr rfl))).trans h44, trivial⟩, hf⟩

end

theorem sclear_step (hp : SPre s) {t : State} (h : SS PT s t) : WP isa (.block clearTop) t (SS PT s) := by
  have hc8 := maskV_byte (show sn0v s < 256 from (s.mem (s.gpr .rdx)).isLt)
  have := (h.2.2.2.sizes hp).2.2.2.2.1
  refine WP.mono (ss_stepW (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rdi, .rax]) (by decide) h
    fun V W R hA h33 _ _ => ?_) fun _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, w30, -⟩ := hA.w
  exact WP.mono (clearTop_ok h.2.1 R (c := (maskV (sn0v s)).setWidth 8) h33 (by rw [w30]; exact hc8)
    (by unfold oRsa; omega)) fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

/-! ## The private-key operation's arguments -/

theorem sargs_step (hp : SPre s) {t : State} (h : SS PT s t) : WP isa (.block privArgs) t (SSet s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, -⟩, -⟩ := h
  obtain ⟨-, w21, w22, w23, w24, w25, w26, -⟩ := hA.w
  refine WP.mono (wp_good (block_good _ rfl rfl) (privArgsS_ok hp L he.rd he.fr R w21 w23 w22 w24 w25 w26))
    fun t2 ⟨⟨k2, L2, _, ⟨W2, R2, hW2, _⟩, h1, h2, h3, h4, h5, h6⟩, sp2, mx2, fs2⟩ => ?_
  have hlt : ∀ i < 14, i < nW := fun i hi => by unfold nW frameBytes; omega
  exact ⟨he.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 fs2, L2,
    fun i hi => (R2.fr i (hlt i hi)).trans (hW2 i hi), h1, h2, h3, h4, h5, h6⟩

end VG.Proof.RsaPss.X86_64

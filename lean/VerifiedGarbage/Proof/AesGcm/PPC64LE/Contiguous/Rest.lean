module

-- separate module: The residual ciphertext and its padded GHASH use a different workspace interval from the fused prefix.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Payload
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # Encrypt and authenticate the contiguous POWER suffix in either layout -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr)
open VG.Proof.AesGcm.PPC64LE.DirectGather (cursors Range PieceOutAt)
variable {V : Reg → Addr} {sp : Addr}

abbrev authRest : Prog isa := .seq (.block [mov .r24 .r18,mov .r25 .r19,.li .r26 0])
  (.seq (absorb 16) (.seq (.block [.li .r0 15,.logic .and .r26 .r19 .r0]) (flush 16)))

theorem authRest_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} {H : Block} (x : List Byte)
    (env : Env V sp s) (L : Lay (V .r29) (V .r30) (V .r31)) (a : x.length%16=0)
    (h : blockAt s.mem (V .r29+BitVec.ofNat 64 240)=H) (src : DataOk (V .r30) (V .r31) s (V .r18) (V .r19).toNat) :
    let y := x++bytesAt s.mem (V .r18) (V .r19).toNat
    WP isa authRest s (TaOut V sp H x (y++zeros (padLen y.length)) s.mem) := by
  intro y
  let u := ((s.write .r24 (s.gpr .r18)).write .r25 (s.gpr .r19)).write .r26 0
  have start : WP isa (.block [mov .r24 .r18,mov .r25 .r19,.li .r26 0]) s (·=u) := by crun [u,mov,BitVec.or_self]
  apply WP.seq
  refine WP.mono start fun next eq => ?_
  subst next
  have ue := env.keep (s' := u) (fun r hr => by
    have z : r≠.r24 ∧ r≠.r25 ∧ r≠.r26 := by revert r;decide
    simp [u,State.write,z.1,z.2.1,z.2.2]) rfl rfl rfl
  have inp : AbsIn V sp 16 H x (V .r18) (V .r19).toNat u :=
    ⟨ue,env.fr .r18 (by decide),env.ofNat (r := .r19) (by decide),by rw [a];rfl,src.of_eq rfl rfl,h⟩
  refine WP.seq (WP.mono (absorb_ok L (.inr rfl) inp) fun t ab => ?_)
  let v := (t.write .r0 15).write .r26 (V .r19 &&& 15)
  have step : WP isa (.block [.li .r0 15,.logic .and .r26 .r19 .r0]) t (·=v) := by
    have reg := ab.env.fr .r19 (by decide)
    crun [v,reg]
  refine WP.seq (WP.mono step fun next eq => ?_)
  subst next
  have ve := ab.env.keep (s' := v) (fun r hr => by
    have z : r≠.r0 ∧ r≠.r26 := by revert r;decide
    simp [v,State.write,z.1,z.2]) rfl rfl rfl
  have hh : blockAt v.mem (V .r29+BitVec.ofNat 64 240)=H :=
    (blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))).trans h
  have mask : v.gpr .r26=BitVec.ofNat 64 (y.length%16) := by
    change V .r19 &&& BitVec.ofNat 64 15=_
    rw [and15];congr 1
    simp [y,length_bytesAt,Nat.add_mod,a]
  refine WP.mono (flush_ok L (.inr rfl) (x := y) ⟨ve,hh⟩ mask) fun z done =>
    ⟨done.env,done.hH,fun initial => done.abs (ab.abs initial),(abs_taFrame ab.frame).trans (t_taFrame done.frame)⟩

/-- Replace the saved source by the public suffix length once the source is in r24. -/
abbrev suffixValues (V : Reg → Addr) (n : Nat) (r : Reg) := if r=.r19 then BitVec.ofNat 64 n else V r

abbrev suffixEnd (V : Reg → Addr) (n : Nat) :=
  cursors (suffixValues V n) (V .r18+BitVec.ofNat 64 (16*(n/16)))

structure RestResult (V : Reg → Addr) (sp S : Addr) (n R k : Nat) (icb H : Block) (x : List Byte) (s t : State) : Prop where
  env : Env (suffixEnd V n) sp t
  cipher : bytesAt t.mem (V .r18) n=Proof.Gcm.xorKs (ciphOf s.mem (V .r29) R) icb k (bytesAt s.mem S n)
  absorbed : let y := x++bytesAt t.mem (V .r18) n
    Absorbed t.mem (V .r30+BitVec.ofNat 64 16) (V .r30+BitVec.ofNat 64 32) H (y++zeros (padLen y.length))
  frame : Frame (crFrame (V .r30) (V .r31) (V .r18) n++taFrame (V .r30) (V .r31)) s.mem t.mem

theorem remaining_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} {S : Addr} {n R k : Nat} {icb H : Block} {x : List Byte}
    (env : Env V sp s) (L : Lay (V .r29) (V .r30) (V .r31)) (ptr : s.gpr .r24=S) (len : s.gpr .r25=BitVec.ofNat 64 n)
    (range : Range V s S (V .r18) n) (rounds : R=10 ∨ R=12 ∨ R=14) (key : V .r28=BitVec.ofNat 64 R)
    (aligned : k%16=0) (xa : x.length%16=0) (h : blockAt s.mem (V .r29+BitVec.ofNat 64 240)=H)
    (a : Absorbed s.mem (V .r30+BitVec.ofNat 64 16) (V .r30+BitVec.ofNat 64 32) H x)
    (ctr : Ctr s.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64) (ciphOf s.mem (V .r29) R) icb k) :
    WP isa VG.Impl.AesGcm.PPC64LE.Contiguous.remaining s (RestResult V sp S n R k icb H x s) := by
  let D := V .r18
  let T := suffixValues V n
  let u := (s.write .r21 D).write .r19 (BitVec.ofNat 64 n)
  have st : WP isa (.block [mov .r21 .r18,mov .r19 .r25]) s (·=u) := by
    have d := env.fr .r18 (by decide)
    crun [u,mov,BitVec.or_self,d,len,D]
  apply WP.seq
  refine WP.mono st fun next eq => ?_
  subst next
  have ue : Env (cursors T D) sp u := by
    refine ⟨?_,env.sp,env.perm.of_eq (s' := u) rfl rfl⟩
    intro r hr
    by_cases eq : r=.r21
    · subst r;simp [u,T,State.write,cursors]
    by_cases el : r=.r19
    · subst r;simp [u,T,State.write,cursors,suffixValues]
    simp [u,T,State.write,cursors,suffixValues,eq,el,env.fr r hr]
  have ru : Range T u S D n := ⟨range.src.of_eq rfl rfl,range.dst.of_eq rfl rfl,range.buffers⟩
  refine WP.seq (WP.mono (cryptRest_wp ue ptr len ru L rounds key aligned ctr) fun v ce => ?_)
  have fr : Frame (crFrame (V .r30) (V .r31) D n) s.mem v.mem := ce.frame
  have abs := a.congr (blockAt_frame fr (stp_crFrame L range.dst (by decide))) (bytesAt_frame fr
    (stp_crFrame L range.dst (by omega)) (by omega))
  have hh := (blockAt_frame fr (fun r hr => (ctx_crFrame L range.dst r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))).trans h
  have rr : (suffixEnd V n .r19).toNat=n := by change (BitVec.ofNat 64 n).toNat=n;exact Nat.mod_eq_of_lt range.src.lt
  have va : DataOk (suffixEnd V n .r30) (suffixEnd V n .r31) v (suffixEnd V n .r18) (suffixEnd V n .r19).toNat := by
    rw [rr];exact range.dst.ok.of_eq ce.rd ce.wr
  refine WP.mono (authRest_wp x ce.env L xa hh va) fun t z => ?_
  have data : bytesAt t.mem D n=bytesAt v.mem D n :=
    bytesAt_frame z.frame (data_taFrame range.dst.ok) (Nat.le_of_lt range.src.lt)
  have auth := z.abs abs
  change Absorbed t.mem _ _ H ((x++bytesAt v.mem D (suffixEnd V n .r19).toNat)++zeros (padLen (x++bytesAt v.mem D (suffixEnd V n .r19).toNat).length)) at auth
  rw [rr,←data] at auth
  exact ⟨z.env,data.trans ce.cipher,auth,(fr.mono fun _ e => List.mem_append_left _ e).trans
    (z.frame.mono fun _ e => List.mem_append_right _ e)⟩

end VG.Proof.AesGcm.PPC64LE.Contiguous

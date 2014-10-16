(* edit *)
load "Process";
local
    val ed = ref "vim"
    val a = ref ""
in
    fun sete e = ed := e
    fun e s = (
        if s <> "" then a := s else ();
        Process.system(!ed^" " ^(!a));
        use(!a)
        )
end

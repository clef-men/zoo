include Vernacinterp

let interp ~state vernac =
  interp
    ~intern:fs_intern
    ~verbosely:(not !Flags.quiet)
    ~st:state
    vernac

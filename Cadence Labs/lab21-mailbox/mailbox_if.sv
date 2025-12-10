interface mailbox_if ;

  timeunit       1ns;
  timeprecision 10ps;

  import ex_trans_pkg::*;

  /////////////////////////////////////////////////////////////////////////////
  // DECLARE AND CONSTRUCT THE mbox UNLIMITED UNPARAMETERIZED MAILBOX
  /////////////////////////////////////////////////////////////////////////////

  mailbox mbox;

  function new();
    mbox = new();
  endfunction

  //////////////////////////////////////////////////////////////////////////
  // RETURN THE NUMBER OF ITEMS IN THE MAILBOX
  //////////////////////////////////////////////////////////////////////////

  function int num() ;
    return mbox.num();
  endfunction : num

  /////////////////////////////////////////////////////////////////////////////
  // BLOCKING PUT
  /////////////////////////////////////////////////////////////////////////////

  task automatic put(ref my_tr_base_c my_tr_base) ;
    my_tr_config_c my_tr_config ;
    my_tr_synch_c  my_tr_synch  ;
    my_tr_comms_c  my_tr_comms  ;

    if ( my_tr_base.get_type() == "my_tr_config_c" )
      begin
        if ( $cast(my_tr_config, my_tr_base) == 0 )
          begin $display("Cannot cast trans class"); $finish(0); end

        // BLOCKING PUT FOR CONFIG
        mbox.put(my_tr_config);

      end
    else if ( my_tr_base.get_type() == "my_tr_synch_c" )
      begin
        if ( $cast(my_tr_synch, my_tr_base) == 0 )
          begin $display("Cannot cast trans class"); $finish(0); end

        // BLOCKING PUT FOR SYNCH
        mbox.put(my_tr_synch);

      end
    else if ( my_tr_base.get_type() == "my_tr_comms_c" )
      begin
        if ( $cast(my_tr_comms, my_tr_base) == 0 )
          begin $display("Cannot cast trans class"); $finish(0); end

        // BLOCKING PUT FOR COMMS
        mbox.put(my_tr_comms);

      end
  endtask : put

  /////////////////////////////////////////////////////////////////////////////
  // NON-BLOCKING PUT
  /////////////////////////////////////////////////////////////////////////////

  function automatic int try_put(ref my_tr_base_c my_tr_base) ;
    my_tr_config_c my_tr_config ;
    my_tr_synch_c  my_tr_synch  ;
    my_tr_comms_c  my_tr_comms  ;

    if ( my_tr_base.get_type() == "my_tr_config_c" )
      begin
        if ( $cast(my_tr_config, my_tr_base) == 0 )
          begin $display("Cannot cast trans class"); return 0; end

        // NON-BLOCKING PUT FOR CONFIG
        return mbox.try_put(my_tr_config);

      end
    else if ( my_tr_base.get_type() == "my_tr_synch_c" )
      begin
        if ( $cast(my_tr_synch, my_tr_base) == 0 )
          begin $display("Cannot cast trans class"); return 0; end

        // NON-BLOCKING PUT FOR SYNCH
        return mbox.try_put(my_tr_synch);

      end
    else if ( my_tr_base.get_type() == "my_tr_comms_c" )
      begin
        if ( $cast(my_tr_comms, my_tr_base) == 0 )
          begin $display("Cannot cast trans class"); return 0; end

        // NON-BLOCKING PUT FOR COMMS
        return mbox.try_put(my_tr_comms);

      end

    return 0; // default
  endfunction : try_put


  ////////////////////////////////////////////////////////////////////////
  // BLOCKING GET
  ////////////////////////////////////////////////////////////////////////

  task automatic get(ref my_tr_base_c my_tr_base) ;
    mbox.get(my_tr_base);
  endtask : get


  ////////////////////////////////////////////////////////////////////////////
  // NON-BLOCKING GET
  ////////////////////////////////////////////////////////////////////////////

  function automatic int try_get(ref my_tr_base_c my_tr_base) ;
    return mbox.try_get(my_tr_base);
  endfunction : try_get


  /////////////////////////////////////////////////////////////////////
  // BLOCKING PEEK
  /////////////////////////////////////////////////////////////////////

  task automatic peek(ref my_tr_base_c my_tr_base) ;
    mbox.peek(my_tr_base);
  endtask : peek


  /////////////////////////////////////////////////////////////////////////////
  // NON-BLOCKING PEEK
  /////////////////////////////////////////////////////////////////////////////

  function automatic int try_peek(ref my_tr_base_c my_tr_base) ;
    return mbox.try_peek(my_tr_base);
  endfunction : try_peek


  modport put_port (import num, put, try_put);
  modport get_port (import num, get, try_get, peek, try_peek);

endinterface : mailbox_if

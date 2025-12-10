module semaphore_m ;

  timeunit 1ns;
  timeprecision 1ns;

  localparam  int unsigned num_users = 2 ; 
  /*localparam*/int unsigned arrival_time_min[num_users]='{default:1};
  /*localparam*/int unsigned arrival_time_max[num_users]='{default:7};
  /*localparam*/int unsigned service_time_min[num_users]='{default:1};
  /*localparam*/int unsigned service_time_max[num_users]='{default:9};

  localparam int unsigned simulation_time_max = 100 ;
  var bit running = 1 ;

  /////////////////////////////////////////////////////////////////
  //  INSTANTIATE A SEMAPHORE AND INITIALIZE WITH ONE KEY
  /////////////////////////////////////////////////////////////////

  semaphore sema = new(1);

  // Shared resource
  task limited_resource
  (
    input int unsigned service_time,
    inout int unsigned clobberable_var
  );
    #service_time;
  endtask

  // User process
  task automatic user
  (
    input string name,
    input int unsigned arrival_time_min, arrival_time_max,
    input int unsigned service_time_min, service_time_max 
  ) ;
    while (running)
      begin
        bit blocking;
        int unsigned arrival_time, service_time;
        int unsigned clobberable_var, clobberable_var_orig;
        bit success;
        success = randomize(blocking, arrival_time, service_time, clobberable_var) with
        {
          arrival_time_min <= arrival_time && arrival_time <= arrival_time_max;
          service_time_min <= service_time && service_time <= service_time_max;
        };
        if (!success) begin 
          $display("randomize failed"); 
          $finish; 
        end

        #arrival_time;
        $display("%t: %s get key %s", $time, name, blocking?"blocking":"nonblock");

        if (blocking)
          //////////////////////////////////////////////////
          //  BLOCKING GET
          //////////////////////////////////////////////////
          sema.get(1);

        else
          //////////////////////////////////////////////////////////////////
          //  NON-BLOCKING GET — RETRY EVERY 1ns UNTIL SUCCESS
          //////////////////////////////////////////////////////////////////
          begin
            bit ok = 0;
            while (!ok) begin
              ok = sema.try_get(1);
              if (!ok) #1ns;
            end
          end

        $display("%t: %s got key", $time, name);

        clobberable_var_orig = clobberable_var;
        limited_resource(service_time, clobberable_var);

        if (clobberable_var !== clobberable_var_orig) begin
          $display("%t: %s clobberable_var got clobbered!", $time, name);
          $display("TEST FAILED");
          $finish(0);
        end

        $display("%t: %s put key", $time, name);

        ////////////////////////////////////
        //  PUT SEMAPHORE KEY BACK
        ////////////////////////////////////
        sema.put(1);

      end
  endtask : user


  // Simulate
  initial begin
    $timeformat ( -9, 0, "ns", 5 ) ;

    ////////////////////////////////////////////////////////////////////////
    // TERMINATE SIMULATION IF SEMAPHORE OBJECT NOT CONSTRUCTED
    ////////////////////////////////////////////////////////////////////////
    if (sema == null) begin
      $display("Semaphore not constructed — TEST FAILED");
      $finish(0);
    end

    // Start users
    for ( int unsigned i=0, string name="user0"; i<num_users; ++i, ++name[4] )
    begin
      fork 
        user( name, arrival_time_min[i], arrival_time_max[i],
                     service_time_min[i], service_time_max[i] ) ;
      join_none
      #1ns ;
    end

    #simulation_time_max running <= 0 ;
    wait fork ;

    $display("TEST COMPLETE");
    $finish(0);
  end

endmodule : semaphore_m

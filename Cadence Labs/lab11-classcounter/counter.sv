///////////////////////////////////////////////////////////////////////////
// (c) Copyright 2013 Cadence Design Systems, Inc. All Rights Reserved.
//
// File name   : counter.sv
// Title       : Simple class
// Project     : SystemVerilog Training
// Created     : 2013-4-8
// Description : Simple counter class
// Notes       :
// 
///////////////////////////////////////////////////////////////////////////

module counterclass;
    class counter;

        int count;
        int max;
        int min;

        function new(int c = 0, int m = 0, int n = 255);
            check_limit(m, n);
            check_set(c);
        endfunction //new

        function void load(int val);
            check_set(val);
            //count = val;
        endfunction //load

        function int getcount();
            return count;
        endfunction //getcount

        function void check_limit(int a, int b);
            if (a > b) begin
                max = a;
                min = b;
            end
            else begin
                max = b;
                min = a;
            end
        endfunction

        function void check_set(int set);
            if (set < min || set > max) begin
                count = min;
                $display("WARNING: %0d outside [%0d..%0d], using min=%0d", 
                          set, min, max, min
                        );
                //$finish; don't need to finish
            end
            else
                count = set;
        endfunction

    endclass //counter

    class upcounter extends counter;

        int carry = 0;
        static int upinstance;

        function new(int c, int m, int n);
            super.new(c, m, n);
            carry = 0;
            upinstance = upinstance + 1;
        endfunction //new()

        function void next();
            carry = 0;
            if (count == max) begin
                count = min;
                carry = 1;
            end
            else begin
                count = count + 1;
            end
            $display("count = %0d, carry = %0d", count, carry);
        endfunction

        static function int getupinstances();
            return upinstance;
        endfunction

    endclass //upcounter extends counter

    class downcounter extends counter;

        int borrow;
        static int downinstance;

        function new(int c, int m, int n);
            super.new(c, m, n);
            borrow = 0;
            downinstance = downinstance + 1;
        endfunction //new()

        function void next();
            borrow = 0;
            if (count == min) begin
                count = max;
                borrow = 1;
            end
            else begin
                count = count - 1;
            end
            $display("count = %0d, borrow = %0d", count, borrow);
        endfunction

        static function int getdowninstances();
            return downinstance;
        endfunction

    endclass //downcounter extends counter

    class timer;

        upcounter hours, minutes, seconds;

        function new(int h, int m, int s);
            hours = new(h, 0, 23);
            minutes = new(m, 0, 59);
            seconds = new(s, 0, 59);
        endfunction //new()

        function void load(int a, int b, int c);
            hours.load(a);
            minutes.load(b);
            seconds.load(c);
        endfunction

        function void showval();
            $display("hours = %0d, minutes = %0d, seconds = %0d", 
                      hours.getcount(), minutes.getcount(), seconds.getcount()
                    );
        endfunction

        function void next();
            seconds.next();
            if (seconds.carry) begin
                minutes.next();
                if (minutes.carry)
                    hours.next();
            end
            showval();
        endfunction

        endclass //timer

endmodule
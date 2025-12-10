timeunit 1ns/1ps;

module dpi;

  // Import C functions from stdlibs.c
  import "DPI-C" function int    system(string cmd);
  import "DPI-C" function string getenv(string name);
  import "DPI-C" function real   sin(real x);

  initial begin
    $display("---- Testing system() ----");
    system("echo 'Hello World'");
    system("date");

    $display("---- Testing getenv(PATH) ----");
    string p = getenv("PATH");
    $display("PATH = %s", p);

    $display("---- Testing sin() ----");
    real PI = 3.1415926535;
    real step = PI/4.0;

    for (int i = 0; i < 8; i++) begin
      real angle = i * step;
      real s = sin(angle);
      $display("sin(%f) = %f", angle, s);
    end
  end

endmodule

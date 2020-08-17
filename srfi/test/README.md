## Adding testing for a new implementation


1. In Makefile add a variable for the repl, and a variable for the flags adding <code>top_srcdir</code> to search path, and setting any other flags needed.

2. Add a new ifeq block to the <code>chose implementation</code> section based on <code>TESTSCHEME</code> environment variable and save Makefile.

3. <code>export TESTSCHEME=<var>repl</var></code>

4. Add a <code>cond-expand</code> block to **hello-test** that imports srfi-64, srfi-9 (if necessary), and defines the values **test-name** [<code> "*implementation*-match-test"</code>] and **scheme-version-name** [<code>(string-append "*implementation*-" (version))</code> or <code>"*implementation*-???"</code> if version number isn't available programatically] and then <code>includes</code> **hello-common.scm**.

5. Run tests with <code>make clean</code> then <code>make hello-test</code>, and trouble-shoot any problems that occur.

6. When tests pass for hello, repeat steps 4 and 5 for **match-test**, this time importing the match library defined for this implementation and <code>include</code> **match-common**. Run tests with <code>make clean</code> and <code>make match-test</code> and <code>mv</code> result to **logs** folder.

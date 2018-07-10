import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4viz.VizGUI;

public final class Alloy2Gurobi {

    public static void main(String[] args) throws Err {
        A4Reporter rep = new A4Reporter() {
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };
        // SINGLE SPEC
        if (args.size != 2) {
            throw new RuntimeException("USAGE: alloy2gurobi myspec.als command#[0-n]");
        }
        String filename = args[0];
        int cmd = Integer.parseInt(args[1]);
        System.out.println("=========== Parsing+Typechecking "+filename+" =============");
        Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
        // SINGLE COMMAND
        if (cmd >= world.getAllCommands().size) {
            throw new RuntimeException("ERROR: command# out of bounds");
        }
        Command command = world.getAllCommands()[cmd];
        System.out.println("============ Command "+command+": ============");

        // TODO extract propositional variable to cnf int-var map
        // (should be in the Translation log, if you set it to the highest level)
        // TODO execute command with to-cnf solver
        // TODO turn the sugarmap and cnf constraints into a gurobipy spec
    }
}

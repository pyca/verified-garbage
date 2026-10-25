// The path of the Node binary running this action, as the step's `path` output.
require("fs").appendFileSync(process.env.GITHUB_OUTPUT, `path=${process.execPath}\n`);

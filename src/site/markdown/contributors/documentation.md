# Documentation Workflow

- Documentation lives under `/src/site/markdown` in the form of Markdown `.md` files. They can be directly edited.
- When adding or removing pages, the corresponding menu entry must be added in removed from `/src/site/site.xml`
- To generate documentation for testing:
  `mvn clean site`
	- It is to be run every time the documentation has been updated.
	- The above creates the HTML files inside `/target/site`
- To also publish a complete documentation version:
  `mvn andrun:run@publish-docs`
	- The above copies `/target/site` to `/docs`
	- GitHub must configured to use `/docs` as the web-site of the project, when the repo is public.
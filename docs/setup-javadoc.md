# Javadoc Setup Guide for GitHub Pages

This guide provides step-by-step instructions for setting up automatic Javadoc generation and deployment to GitHub Pages, based on the CNSim Bitcoin project structure.

## 📋 Prerequisites

- Java project with Maven
- GitHub repository
- Source code with proper Javadoc comments

## 🔧 Step 1: Configure Maven for Javadoc Generation

### 1.1 Update your `pom.xml`

Add the Maven Javadoc plugin to your `pom.xml` in the `<plugins>` section:

```xml
<plugin>
    <groupId>org.apache.maven.plugins</groupId>
    <artifactId>maven-javadoc-plugin</artifactId>
    <version>3.11.1</version>
    <configuration>
        <outputDirectory>${basedir}/docs</outputDirectory>
        <doclint>all,-missing</doclint>
    </configuration>
    <executions>
        <execution>
            <goals>
                <goal>javadoc</goal>
            </goals>
            <id>execution1</id>
            <phase>site</phase>
        </execution>
    </executions>
</plugin>
```

### 1.2 Key Configuration Options

- **`outputDirectory`**: `${basedir}/docs` generates docs in `docs/apidocs/` directory
- **`doclint`**: `all,-missing` enables all checks except missing documentation

## 🏗️ Step 2: Generate Javadoc Locally

### 2.1 Clean and Generate Documentation

```bash
# Clean previous builds and generate fresh Javadoc
mvn clean javadoc:javadoc
```

### 2.2 Verify Local Generation

After running the command, you should see:
- `docs/apidocs/` directory created in project root
- `docs/apidocs/index.html` - main documentation entry point
- Package-specific documentation (e.g., `docs/apidocs/ca/yorku/cmg/cnsim/bitcoin/package-summary.html`)

### 2.3 Test Locally

Open the documentation in your browser:
```bash
# macOS
open docs/apidocs/index.html

# Windows
start docs/apidocs/index.html

# Linux
xdg-open docs/apidocs/index.html
```

## 📄 Step 3: Create Custom Landing Page (Optional)

### 3.1 Create `index.html`

Create a custom landing page in your project root with professional styling:

```html
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>CNSim Bitcoin - API Documentation</title>
    <!-- Add your custom styling here -->
</head>
<body>
    <header>
        <h1>CNSim Bitcoin Simulator</h1>
        <p>Consensus Network Simulator for Bitcoin</p>
    </header>
    
    <main>
        <section>
            <a href="docs/apidocs/ca/yorku/cmg/cnsim/bitcoin/package-summary.html" class="docs-button">
                📚 Explore API Documentation
            </a>
        </section>
    </main>
</body>
</html>
```

### 3.2 Link to Specific Package

Point directly to your main package instead of the generic Javadoc index:
```html
<a href="docs/apidocs/ca/yorku/cmg/cnsim/bitcoin/package-summary.html">Documentation</a>
```

## ⚙️ Step 4: Set Up GitHub Actions

### 4.1 Create Workflow Directory

```bash
mkdir -p .github/workflows
```

### 4.2 Create `deploy-javadoc.yml`

Create `.github/workflows/deploy-javadoc.yml`:

```yaml
name: Deploy Javadoc to GitHub Pages

on:
  push:
    branches: [ main ]
  workflow_dispatch:

permissions:
  contents: read
  pages: write
  id-token: write

concurrency:
  group: "pages"
  cancel-in-progress: true

jobs:
  deploy:
    runs-on: ubuntu-latest
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    steps:
      - uses: actions/checkout@v4
      
      - uses: actions/setup-java@v4
        with:
          distribution: temurin
          java-version: '21'
          cache: maven
          
      - name: Generate Javadoc
        run: mvn -B -DskipTests clean javadoc:javadoc
        
      - name: Upload and Deploy Pages
        uses: actions/upload-pages-artifact@v4
        with:
          path: .
          
      - id: deployment
        uses: actions/deploy-pages@v4
```

## 🚀 Step 5: Enable GitHub Pages

### 5.1 Repository Settings

1. Go to your GitHub repository
2. Click **Settings** tab
3. Scroll to **Pages** section (left sidebar)
4. Under **Source**, select **GitHub Actions**

### 5.2 Deploy

1. Commit and push your changes:
```bash
git add .
git commit -m "Add Javadoc generation and GitHub Pages deployment"
git push origin main
```

2. The GitHub Action will automatically trigger and deploy your site

## 📝 Step 6: Fix Common Javadoc Issues

### 6.1 HTML5 Compatibility

Replace deprecated HTML tags in your Javadoc comments:
```java
// ❌ Don't use
/** This uses <tt>deprecated</tt> tag */

// ✅ Use instead  
/** This uses {@code modern} tag */
```

### 6.2 Fix @throws Tags

Ensure proper @throws syntax:
```java
// ❌ Don't use
/** 
 * @throws The parameter cannot be null
 */

// ✅ Use instead
/**
 * @throws IllegalArgumentException if the parameter is null
 */
```

### 6.3 Author Tags

Place @author tags only at class level, not method level:
```java
// ✅ Correct placement
/**
 * Main Bitcoin simulator class.
 * @author Dr. Sotirios Liaskos
 */
public class BitcoinNode {
    
    /**
     * Process a new block.
     * ❌ Don't put @author here
     */
    public void processBlock() { }
}
```

## 🔍 Step 7: Verify Deployment

### 7.1 Check GitHub Actions

1. Go to **Actions** tab in your repository
2. Verify the workflow completed successfully
3. Check for any error messages

### 7.2 Access Your Documentation

Your documentation will be available at:
```
https://yourusername.github.io/yourrepository/
```

- **Landing page**: Custom `index.html`
- **Full Javadoc**: `/docs/apidocs/`
- **Specific package**: `/docs/apidocs/ca/yorku/cmg/cnsim/bitcoin/package-summary.html`

## 🛠️ Step 8: Maintenance and Updates

### 8.1 Update Documentation

Every time you push to main branch:
1. GitHub Actions automatically regenerates Javadoc
2. Site updates with latest documentation
3. No manual intervention required

### 8.2 Local Development

For local testing:
```bash
# Generate docs locally
mvn clean javadoc:javadoc

# View locally
open docs/apidocs/index.html
```

## 🎉 Benefits of This Setup

✅ **Automated**: Documentation updates automatically with code changes  
✅ **Professional**: Custom landing page with university branding  
✅ **Accessible**: Direct links to relevant package documentation  
✅ **Maintainable**: No manual deployment steps required  
✅ **Standard**: Uses official Maven and GitHub Actions tools  

## 📞 Support

For issues or questions about this setup:
1. Check GitHub Actions logs for deployment errors
2. Verify Maven Javadoc plugin configuration
3. Ensure GitHub Pages is enabled with "GitHub Actions" source
4. Test locally first with `mvn clean javadoc:javadoc`

---

*This guide is based on the CNSim Bitcoin project setup and enhanced for automated GitHub Pages deployment.*
